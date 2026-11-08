/* fullcheck6.c: full-width exact check of a strength-6 Sherwood covering perfect hash family SCPHF(n; k, q, 6) whose
   rows are all affine progressions, written for version 4 of "Large Sherwood covering perfect hash families and new
   covering arrays of strengths three to six" (A. Canli) as a second, separately written check.

   It shares no code with the search programs or with the checkers of the data repository
   (github.com/arhancanli/quantavane-covering-arrays, directory checker/). It shares only the file format: a row is a
   line of k point ids, the point (x1, ..., x5) of AG(5,q) having id ((((x1 q + x2) q + x3) q + x4) q + x5), and an
   element of F_q (q = p^e) is the integer sum d_i p^i of its coefficient digits d_i (d_i is the coefficient of x^i)
   modulo the monic polynomial FIELD_POLY below (the polynomials of the data repository's README convention).

   Method (paper: Theorem 6 = separation criterion, Proposition 14 = Algorithm R, Theorem 17 = shift invariance).
   1. Every row r is certified to be v, A v, A^2 v, ... for an invertible affine map A of AG(5,q): A is solved from
      six consecutive affinely independent points and then checked on every column. A set J of six columns is then
      covered by row r if and only if J - min J is, so the family is an SCPHF if and only if every base set
      B = {0 < x1 < x2 < x3 < x4 < y <= k-1} is covered (Theorem 17).
   2. Fix x1 < x2. In row r put u(x) = P(x) - P(0) and reduce modulo W = <u(x1), u(x2)>: w(x) in F_q^3 = F_q^5 / W.
      If u(x1), u(x2) are dependent, row r covers no base set containing x1, x2 and is skipped for the pair.
   3. Fix the largest column y of B. If w(y) = 0 the row is skipped. Otherwise the six points of B are affinely
      dependent in row r iff w(x3), w(x4), w(y) are linearly dependent in F_q^3, iff x3 and x4 get equal labels or one
      gets the wildcard, where the label of x in (x2, y) is the line through [w(y)] and [w(x)] in PG(2,q), and the
      wildcard if w(x) lies in <w(y)>. (This is Theorem 6 with S = {0, x1, x2, y}: the hyperplanes through the points
      of S are the lines of PG(2,q) through [w(y)].)
   4. Algorithm R: the columns of (x2, y) are split row by row by label, a wildcard column joining every class; the
      pairs {x3, x4} of a class that survives every row that is not skipped are exactly the uncovered base sets with
      these x1, x2, y. Each base set is reached exactly once, from its two least nonzero columns and its largest one.
   5. Every reported base set is confirmed in every row by the rank, over F_p, of the 6e x 6e matrix that represents
      the 6 x 6 matrix with rows (1, P(b)), b in B (multiplication matrices built by polynomial arithmetic; no F_q
      table is used there). A disagreement stops the program (exit 3).
   Work: C(k-1, 4) steps (x1, x2, column x, y) for the whole family, split into x1 ranges ("chunks").

   Usage:
     fullcheck6 q FILE check X1FROM X1TO [THREADS] [TAIL_L]   check base sets with x1 in [X1FROM, X1TO); with TAIL_L,
                                                              only base sets whose largest column is >= TAIL_L
     fullcheck6 q FILE brute KCOLS NROWS                      brute force on the first KCOLS columns and NROWS rows
     fullcheck6 q FILE fastlist KCOLS NROWS                   the fast method on the same subarray (for comparison)
     fullcheck6 q FILE multiples M                            test every base set inside M Z (subfield configurations)
     fullcheck6 q - selftest SEED                             random small families: fast method against brute force
   Output: one line "RESULT {json}" per run (check), or the sorted list of uncovered base sets (brute, fastlist). */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>

#define MAXQ 32
#define MAXN 64
#define NC 5        /* coordinates of a point */
#define WILD 0xFF
#define EAGER 6     /* rows whose reduced points are tabulated for each pair; later rows are reduced on demand */

static int q, p, e;
static int FIELD_POLY[8];  /* monic, low degree first, degree e */
static uint8_t F_ADD[MAXQ][MAXQ], F_SUB[MAXQ][MAXQ], F_MUL[MAXQ][MAXQ], F_INV[MAXQ];

static void die(const char *m) { fprintf(stderr, "fullcheck6: %s\n", m); exit(2); }

/* ---------- the field, by polynomial arithmetic over F_p ---------- */
static void digits(int z, int *d) { for (int i = 0; i < e; i++) { d[i] = z % p; z /= p; } }
static int undigits(const int *d) { int z = 0; for (int i = e - 1; i >= 0; i--) z = z * p + d[i]; return z; }
static int polymulmod(int a, int b) {  /* (a * b) mod FIELD_POLY, schoolbook then reduction from the top */
    int da[8], db[8], c[16] = {0};
    digits(a, da); digits(b, db);
    for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) c[i + j] = (c[i + j] + da[i] * db[j]) % p;
    for (int deg = 2 * e - 2; deg >= e; deg--) {
        int t = c[deg];
        if (!t) continue;
        for (int i = 0; i <= e; i++) c[deg - e + i] = ((c[deg - e + i] - t * FIELD_POLY[i]) % p + p) % p;
    }
    return undigits(c);
}
static int polyadd(int a, int b, int sign) {
    int da[8], db[8], c[8];
    digits(a, da); digits(b, db);
    for (int i = 0; i < e; i++) c[i] = ((da[i] + sign * db[i]) % p + p) % p;
    return undigits(c);
}
static void make_field(void) {
    static const struct { int q, p, e, f[6]; } T[] = {
        {4, 2, 2, {1, 1, 1}}, {8, 2, 3, {1, 1, 0, 1}}, {16, 2, 4, {1, 1, 0, 0, 1}}, {32, 2, 5, {1, 0, 1, 0, 0, 1}},
        {9, 3, 2, {1, 0, 1}}, {27, 3, 3, {1, 2, 0, 1}}, {25, 5, 2, {2, 1, 1}}};
    p = 0;
    for (size_t i = 0; i < sizeof T / sizeof T[0]; i++)
        if (T[i].q == q) { p = T[i].p; e = T[i].e; memcpy(FIELD_POLY, T[i].f, sizeof T[i].f); }
    if (!p) {  /* q must be prime */
        if (q < 2 || q > MAXQ) die("unsupported q");
        for (int d = 2; d * d <= q; d++) if (q % d == 0) die("q is neither prime nor a listed prime power");
        p = q; e = 1; FIELD_POLY[0] = 0; FIELD_POLY[1] = 1;  /* F_p[x]/(x): digits are the integers mod p */
    }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            F_ADD[a][b] = (uint8_t)polyadd(a, b, 1);
            F_SUB[a][b] = (uint8_t)polyadd(a, b, -1);
            F_MUL[a][b] = (uint8_t)(e == 1 ? a * b % p : polymulmod(a, b));
        }
    /* every field axiom, exhaustively */
    for (int a = 0; a < q; a++) {
        if (F_ADD[a][0] != a || F_MUL[a][1] != a || F_MUL[a][0] != 0) die("identity axiom fails");
        int inv = -1;
        for (int b = 0; b < q; b++) {
            if (F_ADD[a][b] != F_ADD[b][a] || F_MUL[a][b] != F_MUL[b][a]) die("commutativity fails");
            if (F_ADD[F_SUB[a][b]][b] != a) die("subtraction fails");
            if (F_MUL[a][b] == 1) inv = b;
            for (int c = 0; c < q; c++)
                if (F_ADD[F_ADD[a][b]][c] != F_ADD[a][F_ADD[b][c]] || F_MUL[F_MUL[a][b]][c] != F_MUL[a][F_MUL[b][c]] ||
                    F_MUL[a][F_ADD[b][c]] != F_ADD[F_MUL[a][b]][F_MUL[a][c]])
                    die("associativity or distributivity fails");
        }
        if (a && inv < 0) die("a nonzero element has no inverse: the polynomial is not irreducible");
        F_INV[a] = (uint8_t)(a ? inv : 0);
    }
}

/* ---------- multiplication matrices over F_p, for the confirmation ---------- */
static int BL[MAXQ][5][5];  /* BL[z][i][j]: coefficient of x^i in z * x^j */
static void make_blocks(void) {
    for (int z = 0; z < q; z++)
        for (int j = 0; j < e; j++) {
            int xj[8] = {0}, d[8];
            xj[j] = 1;
            int prod = (e == 1) ? z : polymulmod(z, undigits(xj));
            digits(prod, d);
            for (int i = 0; i < e; i++) BL[z][i][j] = d[i];
        }
    /* the blocks must multiply like the field: BL[a] BL[b] = BL[ab] (checked for all a, b) */
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int ab = (e == 1) ? a * b % p : polymulmod(a, b);
            for (int i = 0; i < e; i++)
                for (int j = 0; j < e; j++) {
                    int s = 0;
                    for (int l = 0; l < e; l++) s += BL[a][i][l] * BL[b][l][j];
                    if (s % p != BL[ab][i][j]) die("multiplication matrices are not multiplicative");
                }
        }
}
static int powmod(int a, int x) { int r = 1; a %= p; while (x) { if (x & 1) r = r * a % p; a = a * a % p; x >>= 1; } return r; }
/* rank over F_p of the 6e x 6e blow-up of the 6 x 6 matrix M over F_q */
static int blowup_full_rank(const int M[6][6]) {
    int R = 6 * e, A[30][30];
    for (int i = 0; i < 6; i++)
        for (int j = 0; j < 6; j++)
            for (int a = 0; a < e; a++)
                for (int b = 0; b < e; b++) A[i * e + a][j * e + b] = BL[M[i][j]][a][b];
    int rank = 0;
    for (int c = 0; c < R; c++) {
        int piv = -1;
        for (int i = rank; i < R; i++) if (A[i][c] % p) { piv = i; break; }
        if (piv < 0) continue;
        if (piv != rank) for (int j = 0; j < R; j++) { int t = A[piv][j]; A[piv][j] = A[rank][j]; A[rank][j] = t; }
        int iv = powmod(A[rank][c], p - 2);
        for (int i = rank + 1; i < R; i++) {
            int f = A[i][c] % p * iv % p;
            if (f) for (int j = c; j < R; j++) A[i][j] = ((A[i][j] - f * A[rank][j]) % p + p) % p;
        }
        rank++;
    }
    return rank == R;
}

/* ---------- the family ---------- */
static int n, k;
static uint8_t *PT;  /* PT[(r k + x) NC + c]: coordinate c of the point of column x in row r */
static uint8_t *UD;  /* UD[(r k + x) NC + c]: the same minus the point of column 0 */
static const uint8_t *pt_of(int r, int x) { return PT + ((size_t)r * k + x) * NC; }

static void load(const char *file) {
    FILE *f = fopen(file, "r");
    if (!f) die("cannot open the family file");
    size_t cap = 1 << 16, len = 0;
    char *buf = malloc(cap);
    int ch, rows = 0, cols = -1;
    long long qq = (long long)q * q * q * q * q;
    int *ids = NULL;
    size_t idn = 0, idcap = 0;
    for (;;) {  /* read line by line */
        len = 0;
        while ((ch = fgetc(f)) != EOF && ch != '\n') { if (len + 1 >= cap) buf = realloc(buf, cap *= 2); buf[len++] = (char)ch; }
        buf[len] = 0;
        if (len > 0 && buf[0] >= '0' && buf[0] <= '9') {
            int c = 0;
            char *s = buf, *end;
            for (;;) {
                while (*s == ' ' || *s == '\t' || *s == '\r') s++;
                if (!*s) break;
                long long v = strtoll(s, &end, 10);
                if (end == s || v < 0 || v >= qq) die("bad point id");
                if (idn == idcap) ids = realloc(ids, (idcap = idcap ? 2 * idcap : 1 << 16) * sizeof *ids);
                ids[idn++] = (int)v;
                c++;
                s = end;
            }
            if (cols < 0) cols = c;
            else if (c != cols) die("rows of different lengths");
            rows++;
        }
        if (ch == EOF) break;
    }
    fclose(f);
    free(buf);
    if (rows < 1 || rows > MAXN || cols < 6) die("bad array size");
    n = rows; k = cols;
    PT = malloc((size_t)n * k * NC);
    UD = malloc((size_t)n * k * NC);
    for (int r = 0; r < n; r++)
        for (int x = 0; x < k; x++) {
            int v = ids[(size_t)r * k + x];
            for (int c = NC - 1; c >= 0; c--) { PT[((size_t)r * k + x) * NC + c] = (uint8_t)(v % q); v /= q; }
        }
    for (int r = 0; r < n; r++)
        for (int x = 0; x < k; x++)
            for (int c = 0; c < NC; c++)
                UD[((size_t)r * k + x) * NC + c] = F_SUB[pt_of(r, x)[c]][pt_of(r, 0)[c]];
    free(ids);
}

/* ---------- step 1: every row is an affine progression of an invertible affine map ---------- */
static int solve_progression(int r) {
    for (int j0 = 0; j0 + 6 < k; j0++) {
        /* rows (1, P(j0+i)) | (1, P(j0+i+1)), i < 6: Gauss-Jordan gives X with V X = W, V = [(1,P(j0+i))] */
        int A[6][12];
        for (int i = 0; i < 6; i++) {
            const uint8_t *a = pt_of(r, j0 + i), *b = pt_of(r, j0 + i + 1);
            A[i][0] = 1; A[i][6] = 1;
            for (int c = 0; c < NC; c++) { A[i][1 + c] = a[c]; A[i][7 + c] = b[c]; }
        }
        int ok = 1;
        for (int c = 0; c < 6 && ok; c++) {
            int piv = -1;
            for (int i = c; i < 6; i++) if (A[i][c]) { piv = i; break; }
            if (piv < 0) { ok = 0; break; }
            if (piv != c) for (int j = 0; j < 12; j++) { int t = A[piv][j]; A[piv][j] = A[c][j]; A[c][j] = t; }
            int iv = F_INV[A[c][c]];
            for (int j = 0; j < 12; j++) A[c][j] = F_MUL[A[c][j]][iv];
            for (int i = 0; i < 6; i++)
                if (i != c && A[i][c]) { int fct = A[i][c]; for (int j = 0; j < 12; j++) A[i][j] = F_SUB[A[i][j]][F_MUL[fct][A[c][j]]]; }
        }
        if (!ok) continue;  /* these six points lie on a hyperplane; try the next window */
        /* X = A[.][6..11] satisfies (1, P(j+1)) = (1, P(j)) X for the window; as a map on row vectors h -> h X */
        int X[6][6];
        for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) X[i][j] = A[i][6 + j];
        if (X[0][0] != 1) return -1;
        for (int i = 1; i < 6; i++) if (X[i][0] != 0) return -1;  /* not affine */
        /* linear part X[1..5][1..5] must be invertible */
        int L[5][5], rank = 0;
        for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) L[i][j] = X[1 + i][1 + j];
        for (int c = 0; c < 5; c++) {
            int piv = -1;
            for (int i = rank; i < 5; i++) if (L[i][c]) { piv = i; break; }
            if (piv < 0) continue;
            for (int j = 0; j < 5; j++) { int t = L[piv][j]; L[piv][j] = L[rank][j]; L[rank][j] = t; }
            int iv = F_INV[L[rank][c]];
            for (int i = rank + 1; i < 5; i++)
                if (L[i][c]) { int fct = F_MUL[L[i][c]][iv]; for (int j = 0; j < 5; j++) L[i][j] = F_SUB[L[i][j]][F_MUL[fct][L[rank][j]]]; }
            rank++;
        }
        if (rank < 5) return -2;
        for (int j = 0; j + 1 < k; j++) {  /* check (1, P(j)) X = (1, P(j+1)) on every column */
            const uint8_t *a = pt_of(r, j), *b = pt_of(r, j + 1);
            int h[6] = {1, a[0], a[1], a[2], a[3], a[4]};
            for (int c = 1; c < 6; c++) {
                int s = 0;
                for (int i = 0; i < 6; i++) s = F_ADD[s][F_MUL[h[i]][X[i][c]]];
                if (s != b[c - 1]) return -3;
            }
        }
        return j0;
    }
    return -4;
}

/* ---------- PG(2,q): points, and the lines through a point ---------- */
static int NP, ZERO, NPZ;   /* points of PG(2,q); index of the zero vector; NP + 1 */
static uint16_t *PROJ;      /* PROJ[(a q + b) q + c]: index of the point <(a,b,c)>, ZERO for the zero vector */
static uint8_t *LOC;        /* LOC[P NPZ + Q]: index 0..q of the line PQ among the lines through P; WILD if Q = P or ZERO */
static void make_plane(void) {
    NP = q * q + q + 1; ZERO = NP; NPZ = NP + 1;
    int (*rep)[3] = malloc(sizeof *rep * NP), np = 0;
    PROJ = malloc(sizeof(uint16_t) * q * q * q);
    for (int v = 0; v < q * q * q; v++) PROJ[v] = 0xFFFF;
    PROJ[0] = (uint16_t)ZERO;
    /* representatives with first nonzero coordinate 1, listed in increasing order of (a, b, c) */
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++) {
                int lead = a ? a : b ? b : c;
                if (lead != 1) continue;
                rep[np][0] = a; rep[np][1] = b; rep[np][2] = c;
                for (int s = 1; s < q; s++)
                    PROJ[(F_MUL[s][a] * q + F_MUL[s][b]) * q + F_MUL[s][c]] = (uint16_t)np;
                np++;
            }
    if (np != NP) die("wrong number of points of PG(2,q)");
    for (int v = 0; v < q * q * q; v++) if (PROJ[v] == 0xFFFF) die("a vector without a point");
    LOC = malloc((size_t)NPZ * NPZ);
    memset(LOC, WILD, (size_t)NPZ * NPZ);
    for (int P = 0; P < NP; P++) {
        /* two functionals alpha, beta with kernel <P>: a basis of the solutions of h . P = 0 */
        int sol[2][3], ns = 0, piv = 0;
        while (!rep[P][piv]) piv++;
        int ip = F_INV[rep[P][piv]];
        for (int free_c = 0; free_c < 3; free_c++) {
            if (free_c == piv) continue;
            int h[3] = {0, 0, 0};
            h[free_c] = 1;
            /* h[piv] = - rep[P][free_c] / rep[P][piv] */
            h[piv] = F_SUB[0][F_MUL[rep[P][free_c]][ip]];
            memcpy(sol[ns++], h, sizeof h);
        }
        int seen[MAXQ + 1] = {0};
        for (int Q = 0; Q < NP; Q++) {
            if (Q == P) continue;
            int al = 0, be = 0;
            for (int c = 0; c < 3; c++) { al = F_ADD[al][F_MUL[sol[0][c]][rep[Q][c]]]; be = F_ADD[be][F_MUL[sol[1][c]][rep[Q][c]]]; }
            if (!al && !be) die("a point outside <P> with both functionals zero");
            int idx = al ? F_MUL[be][F_INV[al]] : q;  /* the point (al : be) of PG(1,q) */
            LOC[(size_t)P * NPZ + Q] = (uint8_t)idx;
            seen[idx]++;
        }
        for (int i = 0; i <= q; i++) if (seen[i] != q) die("a line through P without q further points");
    }
    free(rep);
}

/* ---------- steps 2 to 5 ---------- */
static size_t Q1POW;  /* (q + 1)^4: entries of the signature table */
typedef struct { int b[6]; } bset;
static int cmpbset(const void *a, const void *b);
struct worker {
    int x1, x2;
    int dead[MAXN];
    int c1[MAXN], c2[MAXN], oc[MAXN][3];  /* pivot and other coordinates of the reduction in each row */
    uint8_t ra[MAXN][NC], rb[MAXN][NC];   /* reduced basis of W in each row */
    int ne, erow[EAGER], slot[MAXN];      /* the first EAGER rows that are not skipped for the pair, and their slots */
    uint16_t *pt;                         /* pt[s k + x]: point index of w(x) in the row of slot s */
    int live[MAXN], nlive, P[MAXN];
    int chk[MAXN], nchk;                  /* rows tested after the signature rows */
    int *cls[MAXN + 2], *srt[MAXN + 2], *wld[MAXN + 2];
    uint8_t *lab[MAXN + 2];
    int y;
    uint16_t *hstamp; uint32_t *hnode; unsigned stamp;  /* direct table of signatures: columns without wildcards */
    uint16_t *nxt;                                      /* nxt[x]: earlier column with the same signature */
    uint16_t *wstamp; uint32_t *wnode;                  /* the same for columns with wildcards (node pool) */
    uint16_t *ncol; uint32_t *nnext; long long npool, cappool;
    long long steps, evals, pairs, uncovered, internal, sigsteps, candidates;
    bset *found; int nfound, capfound;
    long long *pairbuf; int npb, cappb;   /* reported pairs of the current (x1, x2, y), deduplicated */
};

static int reduce_index(const struct worker *W, int r, int x) {  /* point index of w_r(x) */
    const uint8_t *u = UD + ((size_t)r * k + x) * NC;
    int s1 = u[W->c1[r]], s2 = u[W->c2[r]], w[3];
    for (int i = 0; i < 3; i++) {
        int c = W->oc[r][i];
        w[i] = F_SUB[F_SUB[u[c]][F_MUL[s1][W->ra[r][c]]]][F_MUL[s2][W->rb[r][c]]];
    }
    return PROJ[(w[0] * q + w[1]) * q + w[2]];
}

static void setup_pair(struct worker *W) {
    for (int r = 0; r < n; r++) {
        const uint8_t *a = UD + ((size_t)r * k + W->x1) * NC, *b = UD + ((size_t)r * k + W->x2) * NC;
        int A[NC], B[NC], c1 = -1, c2 = -1;
        for (int c = 0; c < NC; c++) { A[c] = a[c]; B[c] = b[c]; }
        for (int c = 0; c < NC; c++) if (A[c]) { c1 = c; break; }
        W->dead[r] = 1;
        if (c1 < 0) continue;
        int iv = F_INV[A[c1]];
        for (int c = 0; c < NC; c++) A[c] = F_MUL[A[c]][iv];
        int fb = B[c1];
        for (int c = 0; c < NC; c++) B[c] = F_SUB[B[c]][F_MUL[fb][A[c]]];
        for (int c = 0; c < NC; c++) if (B[c]) { c2 = c; break; }
        if (c2 < 0) continue;
        iv = F_INV[B[c2]];
        for (int c = 0; c < NC; c++) B[c] = F_MUL[B[c]][iv];
        int fa = A[c2];
        for (int c = 0; c < NC; c++) A[c] = F_SUB[A[c]][F_MUL[fa][B[c]]];
        /* now A has 1 at c1 and 0 at c2, B has 0 at c1 and 1 at c2: u -> u - u[c1] A - u[c2] B kills W */
        W->dead[r] = 0;
        W->c1[r] = c1; W->c2[r] = c2;
        for (int c = 0, i = 0; c < NC; c++) if (c != c1 && c != c2) W->oc[r][i++] = c;
        for (int c = 0; c < NC; c++) { W->ra[r][c] = (uint8_t)A[c]; W->rb[r][c] = (uint8_t)B[c]; }
    }
    W->ne = 0;
    for (int r = 0; r < n; r++) {
        W->slot[r] = -1;
        if (W->dead[r] || W->ne == EAGER) continue;
        W->slot[r] = W->ne;
        W->erow[W->ne] = r;
        uint16_t *dst = W->pt + (size_t)W->ne * k;
        for (int x = W->x2 + 1; x < k; x++) dst[x] = (uint16_t)reduce_index(W, r, x);
        W->ne++;
    }
}

static inline int point_of(const struct worker *W, int r, int x) {
    int s = W->slot[r];
    return s >= 0 ? W->pt[(size_t)s * k + x] : reduce_index(W, r, x);
}

static int confirm_uncovered(const int *B) {  /* 1 if B is affinely dependent in every row (blow-up ranks) */
    for (int r = 0; r < n; r++) {
        int M[6][6];
        for (int i = 0; i < 6; i++) {
            const uint8_t *P = pt_of(r, B[i]);
            M[i][0] = 1;
            for (int c = 0; c < NC; c++) M[i][1 + c] = P[c];
        }
        if (blowup_full_rank(M)) return 0;
    }
    return 1;
}

static void report_pairs(struct worker *W, const int *mem, int sz) {
    for (int i = 0; i < sz; i++)
        for (int j = i + 1; j < sz; j++) {
            int a = mem[i] < mem[j] ? mem[i] : mem[j], b = mem[i] ^ mem[j] ^ a;
            if (W->npb == W->cappb) W->pairbuf = realloc(W->pairbuf, sizeof(long long) * (W->cappb = W->cappb ? 2 * W->cappb : 1024));
            W->pairbuf[W->npb++] = (long long)a << 32 | (unsigned)b;
        }
}

static void refine(struct worker *W, int depth, const int *mem, int sz) {
    if (depth == W->nlive) { report_pairs(W, mem, sz); return; }
    int r = W->live[depth];
    const uint8_t *loc = LOC + (size_t)W->P[r] * NPZ;
    uint8_t *lb = W->lab[depth];
    int cnt[MAXQ + 2], start[MAXQ + 2];
    memset(cnt, 0, sizeof(int) * (q + 2));
    W->evals += sz;
    if (W->slot[r] >= 0) {
        const uint16_t *pr = W->pt + (size_t)W->slot[r] * k;
        for (int i = 0; i < sz; i++) { uint8_t l = loc[pr[mem[i]]]; lb[i] = l; cnt[l == WILD ? q + 1 : l]++; }
    } else {
        for (int i = 0; i < sz; i++) { uint8_t l = loc[reduce_index(W, r, mem[i])]; lb[i] = l; cnt[l == WILD ? q + 1 : l]++; }
    }
    int nw = cnt[q + 1], s = 0;
    for (int l = 0; l <= q; l++) { start[l] = s; s += cnt[l]; }
    int *srt = W->srt[depth], *wld = W->wld[depth], wi = 0;
    for (int i = 0; i < sz; i++) { if (lb[i] == WILD) wld[wi++] = mem[i]; else srt[start[lb[i]]++] = mem[i]; }
    int *child = W->cls[depth + 1], any = 0;
    for (int l = 0, off = 0; l <= q; off += cnt[l], l++) {
        if (!cnt[l]) continue;
        any = 1;
        if (cnt[l] + nw < 2) continue;
        memcpy(child, srt + off, sizeof(int) * cnt[l]);
        memcpy(child + cnt[l], wld, sizeof(int) * nw);
        refine(W, depth + 1, child, cnt[l] + nw);
    }
    if (!any && nw >= 2) { memcpy(child, wld, sizeof(int) * nw); refine(W, depth + 1, child, nw); }
}

static int cmpll(const void *a, const void *b) { long long x = *(const long long *)a, y = *(const long long *)b; return (x > y) - (x < y); }

static int USE_REFINE = 0;  /* 1: Algorithm R only (reference path for the tests) */
static int RSIG = 4;        /* signature rows */

static void finish_y(struct worker *W, int y) {  /* deduplicate the reported pairs and confirm each set */
    if (!W->npb) return;
    qsort(W->pairbuf, W->npb, sizeof(long long), cmpll);
    for (int i = 0; i < W->npb; i++) {
        if (i && W->pairbuf[i] == W->pairbuf[i - 1]) continue;
        W->pairs++;
        int B[6] = {0, W->x1, W->x2, (int)(W->pairbuf[i] >> 32), (int)(W->pairbuf[i] & 0xFFFFFFFF), y};
        if (!confirm_uncovered(B)) { W->internal++; fprintf(stderr, "INTERNAL: %d %d %d %d %d %d reported but covered\n", B[0], B[1], B[2], B[3], B[4], B[5]); continue; }
        W->uncovered++;
        if (W->nfound == W->capfound) W->found = realloc(W->found, sizeof(bset) * (W->capfound = W->capfound ? 2 * W->capfound : 64));
        if (W->nfound < 100000) { memcpy(W->found[W->nfound].b, B, sizeof B); W->nfound++; }
    }
}

static inline void add_pair(struct worker *W, int a, int b) {
    if (W->npb == W->cappb) W->pairbuf = realloc(W->pairbuf, sizeof(long long) * (W->cappb = W->cappb ? 2 * W->cappb : 1024));
    W->pairbuf[W->npb++] = (long long)a << 32 | (unsigned)b;
}

/* a pair with equal signatures (wildcards matching every label): test it in the other rows; rows that are not
   tabulated get their point of y on first use, and a row with w(y) = 0 is skipped */
static inline void check_pair(struct worker *W, int z, int x) {
    W->candidates++;
    for (int i = 0; i < W->nchk; i++) {
        int r = W->chk[i];
        if (W->P[r] < 0) W->P[r] = reduce_index(W, r, W->y);
        if (W->P[r] == ZERO) continue;
        const uint8_t *L = LOC + (size_t)W->P[r] * NPZ;
        unsigned a = L[point_of(W, r, z)], b = L[point_of(W, r, x)];
        if (a != b && a != WILD && b != WILD) return;
    }
    add_pair(W, z < x ? z : x, z < x ? x : z);
}

static inline void wild_insert(struct worker *W, unsigned key, int x) {  /* probe both tables, enter x in the wild one */
    if (W->hstamp[key] == W->stamp)
        for (int z = W->hnode[key] & 0xFFFF; z != 0xFFFF; z = W->nxt[z]) check_pair(W, z, x);
    if (W->npool == W->cappool) {
        W->cappool = W->cappool ? 2 * W->cappool : 1 << 12;
        W->ncol = realloc(W->ncol, sizeof(uint16_t) * W->cappool);
        W->nnext = realloc(W->nnext, sizeof(uint32_t) * W->cappool);
    }
    uint32_t nd = (uint32_t)W->npool++, nx = 0xFFFFFFFFu;
    if (W->wstamp[key] == W->stamp) {
        for (uint32_t t = W->wnode[key]; t != 0xFFFFFFFFu; t = W->nnext[t]) check_pair(W, W->ncol[t], x);
        nx = W->wnode[key];
    }
    W->ncol[nd] = (uint16_t)x; W->nnext[nd] = nx;
    W->wnode[key] = nd; W->wstamp[key] = (uint16_t)W->stamp;
}

static void do_y(struct worker *W, int y) {
    W->y = y;
    int m = y - W->x2 - 1;
    W->steps += m;
    if (m < 2) return;
    W->npb = 0;
    int sig[8], ns = 0;
    for (int r = 0; r < n; r++) W->P[r] = -1;
    if (!USE_REFINE)
        for (int s = 0; s < W->ne && ns < RSIG; s++) {
            int r = W->erow[s], P = W->pt[(size_t)s * k + y];
            W->P[r] = P;
            if (P != ZERO) sig[ns++] = r;
        }
    if (USE_REFINE || ns < RSIG) {  /* Algorithm R over all rows that are not skipped */
        W->nlive = 0;
        for (int r = 0; r < n; r++) {
            if (W->dead[r]) continue;
            int P = point_of(W, r, y);
            if (P == ZERO) continue;
            W->P[r] = P;
            W->live[W->nlive++] = r;
        }
        int *mem = W->cls[0];
        for (int i = 0; i < m; i++) mem[i] = W->x2 + 1 + i;
        refine(W, 0, mem, m);
        finish_y(W, y);
        return;
    }
    /* the other rows that are not skipped for the pair are tested for the candidates, tabulated rows first */
    W->nchk = 0;
    for (int pass = 0; pass < 2; pass++)
        for (int r = 0; r < n; r++) {
            if (W->dead[r] || (W->slot[r] >= 0) != (pass == 0)) continue;
            int is_sig = 0;
            for (int j = 0; j < RSIG; j++) if (sig[j] == r) is_sig = 1;
            if (!is_sig) W->chk[W->nchk++] = r;
        }
    if (++W->stamp == 0x10000) {
        memset(W->hstamp, 0, sizeof(uint16_t) * Q1POW);
        memset(W->wstamp, 0, sizeof(uint16_t) * Q1POW);
        W->stamp = 1;
    }
    W->npool = 0;
    W->sigsteps += m;
    const unsigned Q1 = (unsigned)q + 1, st = W->stamp;
    const uint16_t *p0 = W->pt + (size_t)W->slot[sig[0]] * k, *p1 = W->pt + (size_t)W->slot[sig[1]] * k,
                   *p2 = W->pt + (size_t)W->slot[sig[2]] * k, *p3 = RSIG > 3 ? W->pt + (size_t)W->slot[sig[3]] * k : p2;
    const uint8_t *L0 = LOC + (size_t)W->P[sig[0]] * NPZ, *L1 = LOC + (size_t)W->P[sig[1]] * NPZ,
                  *L2 = LOC + (size_t)W->P[sig[2]] * NPZ, *L3 = RSIG > 3 ? LOC + (size_t)W->P[sig[3]] * NPZ : L2;
    uint16_t *hs = W->hstamp, *nxt = W->nxt;
    uint32_t *hn = W->hnode;
    int *wl = W->wld[0], nw = 0;
    uint8_t *lb = W->lab[0];
    /* columns without wildcards: a direct table of signatures, a chain of earlier columns per signature */
    for (int x = W->x2 + 1; x < y; x++) {
        unsigned a = L0[p0[x]], b = L1[p1[x]], c = L2[p2[x]], d = RSIG > 3 ? L3[p3[x]] : 0;
        if ((a | b | c | d) & 0x80) {
            uint8_t *l = lb + 4 * nw;
            l[0] = (uint8_t)a; l[1] = (uint8_t)b; l[2] = (uint8_t)c; l[3] = (uint8_t)d;
            wl[nw++] = x;
            continue;
        }
        unsigned key = ((a * Q1 + b) * Q1 + c) * Q1 + d;
        if (hs[key] == st) {
            int z = hn[key] & 0xFFFF;
            nxt[x] = (uint16_t)z;
            for (; z != 0xFFFF; z = nxt[z]) check_pair(W, z, x);
        } else {
            hs[key] = (uint16_t)st;
            nxt[x] = 0xFFFF;
        }
        hn[key] = (uint32_t)x;
    }
    /* columns with wildcards, entered under every signature they match: they meet every column without wildcards
       there, and every earlier column with wildcards at a signature that both match */
    for (int i = 0; i < nw; i++) {
        int x = wl[i];
        const uint8_t *l = lb + 4 * i;
        unsigned lo[4], hi[4];
        for (int j = 0; j < 4; j++) {
            if (j >= RSIG) { lo[j] = hi[j] = 0; continue; }
            if (l[j] == WILD) { lo[j] = 0; hi[j] = (unsigned)q; } else lo[j] = hi[j] = l[j];
        }
        for (unsigned a = lo[0]; a <= hi[0]; a++)
            for (unsigned b = lo[1]; b <= hi[1]; b++)
                for (unsigned c = lo[2]; c <= hi[2]; c++)
                    for (unsigned d = lo[3]; d <= hi[3]; d++) wild_insert(W, ((a * Q1 + b) * Q1 + c) * Q1 + d, x);
    }
    finish_y(W, y);
}

static struct worker *new_worker(void) {
    struct worker *W = calloc(1, sizeof *W);
    W->pt = malloc(sizeof(uint16_t) * (size_t)EAGER * k);
    W->hstamp = calloc(Q1POW, sizeof(uint16_t));
    W->hnode = malloc(sizeof(uint32_t) * Q1POW);
    W->wstamp = calloc(Q1POW, sizeof(uint16_t));
    W->wnode = malloc(sizeof(uint32_t) * Q1POW);
    W->nxt = malloc(sizeof(uint16_t) * k);
    for (int d = 0; d < MAXN + 2; d++) {
        W->cls[d] = malloc(sizeof(int) * k); W->srt[d] = malloc(sizeof(int) * k); W->wld[d] = malloc(sizeof(int) * k);
        W->lab[d] = malloc((size_t)4 * k);
    }
    return W;
}

/* ---------- the chunk: pairs (x1, x2) with X1FROM <= x1 < X1TO, shared by the threads ---------- */
static int X1FROM, X1TO, TAIL;
static long long NEXT_PAIR, NPAIRS;
static long long *PAIR_BASE;
static pthread_mutex_t MX = PTHREAD_MUTEX_INITIALIZER;

static void *thread_main(void *arg) {
    struct worker *W = arg;
    for (;;) {
        pthread_mutex_lock(&MX);
        long long idx = NEXT_PAIR < NPAIRS ? NEXT_PAIR++ : -1;
        pthread_mutex_unlock(&MX);
        if (idx < 0) break;
        int lo = 0, hi = X1TO - X1FROM - 1;  /* find x1: PAIR_BASE[i] <= idx < PAIR_BASE[i+1] */
        while (lo < hi) { int mid = (lo + hi + 1) / 2; if (PAIR_BASE[mid] <= idx) lo = mid; else hi = mid - 1; }
        W->x1 = X1FROM + lo;
        W->x2 = W->x1 + 1 + (int)(idx - PAIR_BASE[lo]);
        int ystart = W->x2 + 3;
        if (TAIL > ystart) ystart = TAIL;
        if (ystart > k - 1) continue;
        setup_pair(W);
        for (int y = ystart; y < k; y++) do_y(W, y);
    }
    return NULL;
}

static double cpu_seconds(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return ru.ru_utime.tv_sec + ru.ru_utime.tv_usec * 1e-6 + ru.ru_stime.tv_sec + ru.ru_stime.tv_usec * 1e-6;
}
static double wall_seconds(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }

static long long expected_steps(void) {  /* sum over the chunk of the number of (x1, x2, x, y) with x2 < x < y */
    long long s = 0;
    for (int x1 = X1FROM; x1 < X1TO; x1++)
        for (int x2 = x1 + 1; x2 <= k - 4; x2++) {
            long long ys = x2 + 3 > TAIL ? x2 + 3 : TAIL;
            if (ys > k - 1) continue;
            long long lo = ys - x2 - 1, hi = (long long)k - x2 - 2;  /* sum of d for d = lo..hi */
            s += (lo + hi) * (hi - lo + 1) / 2;
        }
    return s;
}

static int run_check(int threads) {
    if (X1FROM < 1) X1FROM = 1;
    if (X1TO > k - 4) X1TO = k - 4;
    if (X1TO <= X1FROM) die("empty chunk");
    int span = X1TO - X1FROM;
    PAIR_BASE = malloc(sizeof(long long) * (span + 1));
    NPAIRS = 0;
    for (int i = 0; i < span; i++) { PAIR_BASE[i] = NPAIRS; NPAIRS += (k - 4) - (X1FROM + i); }
    PAIR_BASE[span] = NPAIRS;
    NEXT_PAIR = 0;
    struct worker *Ws[256];
    pthread_t th[256];
    if (threads < 1) threads = 1;
    if (threads > 256) threads = 256;
    double w0 = wall_seconds(), c0 = cpu_seconds();
    for (int i = 0; i < threads; i++) { Ws[i] = new_worker(); pthread_create(&th[i], NULL, thread_main, Ws[i]); }
    long long steps = 0, evals = 0, pairs = 0, unc = 0, internal = 0, cands = 0;
    int nf = 0;
    bset *all = NULL;
    for (int i = 0; i < threads; i++) {
        pthread_join(th[i], NULL);
        steps += Ws[i]->steps; evals += Ws[i]->evals; cands += Ws[i]->candidates; pairs += Ws[i]->pairs; unc += Ws[i]->uncovered; internal += Ws[i]->internal;
        all = realloc(all, sizeof(bset) * (nf + Ws[i]->nfound + 1));
        memcpy(all + nf, Ws[i]->found, sizeof(bset) * Ws[i]->nfound);
        nf += Ws[i]->nfound;
    }
    double wall = wall_seconds() - w0, cpu = cpu_seconds() - c0;
    long long exp = expected_steps();
    if (nf > 1) qsort(all, nf, sizeof(bset), cmpbset);
    printf("RESULT {\"q\": %d, \"n\": %d, \"k\": %d, \"x1_from\": %d, \"x1_to\": %d, \"tail\": %d, \"steps\": %lld, "
           "\"expected_steps\": %lld, \"label_evaluations\": %lld, \"candidate_pairs\": %lld, \"pairs_reported\": %lld, \"uncovered_base_sets\": %lld, "
           "\"internal_disagreements\": %lld, \"threads\": %d, \"wall_seconds\": %.1f, \"cpu_seconds\": %.1f, \"first_sets\": [",
           q, n, k, X1FROM, X1TO, TAIL, steps, exp, evals, cands, pairs, unc, internal, threads, wall, cpu);
    for (int i = 0; i < nf && i < 50; i++)
        printf("%s[%d, %d, %d, %d, %d, %d]", i ? ", " : "", all[i].b[0], all[i].b[1], all[i].b[2], all[i].b[3], all[i].b[4], all[i].b[5]);
    printf("]}\n");
    fflush(stdout);
    if (internal) return 3;
    if (steps != exp) { fprintf(stderr, "step count %lld differs from the expected %lld\n", steps, exp); return 3; }
    return unc ? 1 : 0;
}

/* ---------- brute force and listing (for tests) ---------- */
static int cmpb(const void *a, const void *b) { return memcmp(a, b, sizeof(bset)); }
static int cmpbset(const void *a, const void *b) {
    const int *x = ((const bset *)a)->b, *y = ((const bset *)b)->b;
    for (int i = 0; i < 6; i++) if (x[i] != y[i]) return x[i] < y[i] ? -1 : 1;
    return 0;
}
static void brute_list(void) {
    int B[6] = {0};
    long long cnt = 0;
    for (B[1] = 1; B[1] < k; B[1]++)
        for (B[2] = B[1] + 1; B[2] < k; B[2]++)
            for (B[3] = B[2] + 1; B[3] < k; B[3]++)
                for (B[4] = B[3] + 1; B[4] < k; B[4]++)
                    for (B[5] = B[4] + 1; B[5] < k; B[5]++)
                        if (confirm_uncovered(B)) { printf("%d %d %d %d %d %d\n", B[0], B[1], B[2], B[3], B[4], B[5]); cnt++; }
    fprintf(stderr, "brute: %lld uncovered base sets\n", cnt);
}
static void fast_list(void) {
    X1FROM = 1; X1TO = k - 4; TAIL = 0;
    struct worker *W = new_worker();
    for (int x1 = 1; x1 <= k - 5; x1++)
        for (int x2 = x1 + 1; x2 <= k - 4; x2++) {
            W->x1 = x1; W->x2 = x2;
            setup_pair(W);
            for (int y = x2 + 3; y < k; y++) do_y(W, y);
        }
    qsort(W->found, W->nfound, sizeof(bset), cmpbset);
    for (int i = 0; i < W->nfound; i++) printf("%d %d %d %d %d %d\n", W->found[i].b[0], W->found[i].b[1], W->found[i].b[2], W->found[i].b[3], W->found[i].b[4], W->found[i].b[5]);
    fprintf(stderr, "fast: %lld uncovered base sets, %lld internal disagreements\n", W->uncovered, W->internal);
    if (W->internal) exit(3);
}

/* restrict the loaded family to its first KC columns and NR rows */
static void restrict_to(int KC, int NR) {
    if (KC > k || NR > n || KC < 6 || NR < 1) die("bad restriction");
    uint8_t *P2 = malloc((size_t)NR * KC * NC), *U2 = malloc((size_t)NR * KC * NC);
    for (int r = 0; r < NR; r++) {
        memcpy(P2 + (size_t)r * KC * NC, PT + (size_t)r * k * NC, (size_t)KC * NC);
        memcpy(U2 + (size_t)r * KC * NC, UD + (size_t)r * k * NC, (size_t)KC * NC);
    }
    free(PT); free(UD); PT = P2; UD = U2; n = NR; k = KC;
}

/* ---------- self-test: random families of affine progressions, fast against brute force ---------- */
static uint64_t RS = 88172645463325252ULL;
static uint64_t rnd(void) { RS ^= RS << 13; RS ^= RS >> 7; RS ^= RS << 17; return RS; }
static void random_family(int NR, int KC) {
    n = NR; k = KC;
    free(PT); free(UD);
    PT = malloc((size_t)n * k * NC); UD = malloc((size_t)n * k * NC);
    for (int r = 0; r < n; r++) {
        int M[5][5], b[5], v[5], rank;
        do {  /* a random invertible linear part */
            int L[5][5];
            for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) L[i][j] = M[i][j] = (int)(rnd() % q);
            rank = 0;
            for (int c = 0; c < 5; c++) {
                int piv = -1;
                for (int i = rank; i < 5; i++) if (L[i][c]) { piv = i; break; }
                if (piv < 0) continue;
                for (int j = 0; j < 5; j++) { int t = L[piv][j]; L[piv][j] = L[rank][j]; L[rank][j] = t; }
                int iv = F_INV[L[rank][c]];
                for (int i = rank + 1; i < 5; i++) if (L[i][c]) { int f = F_MUL[L[i][c]][iv]; for (int j = 0; j < 5; j++) L[i][j] = F_SUB[L[i][j]][F_MUL[f][L[rank][j]]]; }
                rank++;
            }
        } while (rank < 5);
        for (int i = 0; i < 5; i++) { b[i] = (int)(rnd() % q); v[i] = (int)(rnd() % q); }
        if (r % 3 == 2) for (int i = 0; i < 5; i++) b[i] = 0;  /* some rows linear */
        for (int x = 0; x < k; x++) {
            for (int c = 0; c < NC; c++) PT[((size_t)r * k + x) * NC + c] = (uint8_t)v[c];
            int w[5];
            for (int i = 0; i < 5; i++) {
                int s = b[i];
                for (int j = 0; j < 5; j++) s = F_ADD[s][F_MUL[M[i][j]][v[j]]];
                w[i] = s;
            }
            memcpy(v, w, sizeof v);
        }
    }
    for (int r = 0; r < n; r++)
        for (int x = 0; x < k; x++)
            for (int c = 0; c < NC; c++) UD[((size_t)r * k + x) * NC + c] = F_SUB[PT[((size_t)r * k + x) * NC + c]][PT[(size_t)r * k * NC + c]];
}
static int selftest(int seed) {
    RS ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    int total_sets = 0;
    for (int trial = 0; trial < 12; trial++) {
        int NR = 1 + trial % 6, KC = 18 + (int)(rnd() % 10);
        random_family(NR, KC);
        for (int r = 0; r < n; r++) if (solve_progression(r) < 0) { fprintf(stderr, "selftest: random row %d not certified\n", r); /* allowed: tiny orbits */ }
        /* brute force */
        bset *bf = NULL; int nb = 0, cap = 0;
        int B[6] = {0};
        for (B[1] = 1; B[1] < k; B[1]++) for (B[2] = B[1] + 1; B[2] < k; B[2]++) for (B[3] = B[2] + 1; B[3] < k; B[3]++)
            for (B[4] = B[3] + 1; B[4] < k; B[4]++) for (B[5] = B[4] + 1; B[5] < k; B[5]++)
                if (confirm_uncovered(B)) { if (nb == cap) bf = realloc(bf, sizeof(bset) * (cap = cap ? 2 * cap : 256)); memcpy(bf[nb++].b, B, sizeof B); }
        int same = 1, got[2] = {0, 0};
        for (int method = 0; method < 2; method++) {  /* 0: signature table, 1: Algorithm R */
            USE_REFINE = method;
            struct worker *W = new_worker();
            for (int x1 = 1; x1 <= k - 5; x1++)
                for (int x2 = x1 + 1; x2 <= k - 4; x2++) { W->x1 = x1; W->x2 = x2; setup_pair(W); for (int y = x2 + 3; y < k; y++) do_y(W, y); }
            qsort(W->found, W->nfound, sizeof(bset), cmpbset);
            got[method] = W->nfound;
            if (!((nb == W->nfound) && (nb == 0 || memcmp(bf, W->found, sizeof(bset) * nb) == 0) && !W->internal)) same = 0;
        }
        USE_REFINE = 0;
        fprintf(stderr, "selftest q %d trial %d: %d rows, %d columns: brute %d, signature %d, Algorithm R %d uncovered base sets: %s\n", q, trial, n, k, nb, got[0], got[1], same ? "agree" : "DISAGREE");
        if (!same) return 1;
        total_sets += nb;
        free(bf);
    }
    fprintf(stderr, "selftest q %d (signature rows %d): 12 random families, brute force, signature table and Algorithm R agree (%d uncovered base sets in all)\n", q, RSIG, total_sets);
    (void)cmpb;
    return 0;
}

/* ---------- base sets inside M Z ---------- */
static int multiples(int M) {
    int cnt = 0, B[6] = {0};
    int idx[6];
    long long tested = 0, unc = 0;
    int nm = (k - 1) / M;  /* multiples M, 2M, ..., nm M */
    (void)cnt;
    for (idx[1] = 1; idx[1] <= nm; idx[1]++) for (idx[2] = idx[1] + 1; idx[2] <= nm; idx[2]++)
        for (idx[3] = idx[2] + 1; idx[3] <= nm; idx[3]++) for (idx[4] = idx[3] + 1; idx[4] <= nm; idx[4]++)
            for (idx[5] = idx[4] + 1; idx[5] <= nm; idx[5]++) {
                for (int i = 1; i < 6; i++) B[i] = idx[i] * M;
                tested++;
                if (confirm_uncovered(B)) { unc++; if (unc <= 20) printf("uncovered: %d %d %d %d %d %d\n", B[0], B[1], B[2], B[3], B[4], B[5]); }
            }
    printf("MULTIPLES {\"q\": %d, \"n\": %d, \"k\": %d, \"M\": %d, \"base_sets_tested\": %lld, \"uncovered\": %lld}\n", q, n, k, M, tested, unc);
    return unc ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: see the head of fullcheck6.c\n"); return 2; }
    q = atoi(argv[1]);
    make_field();
    make_blocks();
    make_plane();
    Q1POW = (size_t)(q + 1) * (q + 1) * (q + 1) * (q + 1);
    if (getenv("FC_RSIG")) RSIG = atoi(getenv("FC_RSIG"));
    if (RSIG < 3 || RSIG > 4) die("FC_RSIG must be 3 or 4");
    if (getenv("FC_REFINE")) USE_REFINE = atoi(getenv("FC_REFINE"));
    const char *mode = argv[3];
    if (!strcmp(mode, "selftest")) return selftest(argc > 4 ? atoi(argv[4]) : 1);
    load(argv[2]);
    if (!strcmp(mode, "brute") || !strcmp(mode, "fastlist")) {
        if (argc < 6) die("brute/fastlist need KCOLS NROWS");
        restrict_to(atoi(argv[4]), atoi(argv[5]));
        if (!strcmp(mode, "brute")) brute_list(); else fast_list();
        return 0;
    }
    int bad = 0;
    for (int r = 0; r < n; r++) {
        int j0 = solve_progression(r);
        if (j0 < 0) { fprintf(stderr, "row %d is not certified as a progression of an invertible affine map (code %d)\n", r, j0); bad++; }
    }
    printf("PROGRESSIONS {\"q\": %d, \"n\": %d, \"k\": %d, \"rows_certified\": %d}\n", q, n, k, n - bad);
    fflush(stdout);
    if (bad) return 4;
    if (!strcmp(mode, "multiples")) return multiples(atoi(argv[4]));
    if (!strcmp(mode, "check")) {
        if (argc < 6) die("check needs X1FROM X1TO");
        X1FROM = atoi(argv[4]); X1TO = atoi(argv[5]);
        int threads = argc > 6 ? atoi(argv[6]) : 1;
        TAIL = argc > 7 ? atoi(argv[7]) : 0;
        return run_check(threads);
    }
    die("unknown mode");
    return 2;
}
