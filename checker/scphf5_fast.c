/* Fast independent check of a strength-5 Sherwood CPHF, SCPHF(n; k, q^4, 5): any five columns must hold, in some row,
   five points of AG(4,q) not on one hyperplane. Written apart from the searches (engine/native) and from
   independent/scphf5_check.c, with the same conventions: points as ids ((x q + y) q + z) q + w, field arithmetic by
   Horner multiplication modulo the listed polynomial (field axioms tested before use). Same method as
   independent/scphf6_fast.c, one dimension down.
   1. Geometry of every set of five columns, two exact methods:
      "brute" tries all C(k,5) sets (Gaussian elimination in every row).
      "fast" uses the rows that are affine progressions v, Tv, T^2 v, ... for an invertible affine map T (solved from
      five consecutive points and checked on every point): a set fails in all of these "cyclic" rows exactly when its
      shift by minus its first column does, so each base set {0 < x1 < x2 < x3 < x4} is reached once, from its two
      smallest other columns. With u_r(x) = column x's point minus column 0's in cyclic row r, the five points lie on
      one hyperplane exactly when u_r(x1), ..., u_r(x4) have rank at most 3.
        Column x1: modulo <u(x1)> every column x gets a point pt(x) of PG(2,q), or Z when u(x) is in <u(x1)>
        (Gaussian elimination; a row where u(x1) = 0 fails for every such set and is dropped).
        Pair x1 < x2: with P = pt(x2) (P = Z drops the row: rank <= 1 + 2) the hyperplanes through column 0, x1, x2
        form a pencil, one for each line of PG(2,q) through P; columns x3, x4 fail in the row exactly when pt(x3),
        pt(x4) lie on one line through P, or one of them is P or Z ("wild"). So each column x > x2 has a class per
        row, LINE[P][pt(x)], and the failing pairs are those whose classes agree, or one is wild, in every row; they
        are found as in scphf6_fast.c (signatures of the classes in the rows with the fewest wild columns, a table
        indexed by the signature, wild columns entered under every signature they match, pairs of wild columns on
        the next rows, every candidate tested in the other rows).
      Every failing base set is confirmed by Gaussian elimination in every cyclic row, then each of its shifts that
      fits is tested in the other rows (a 4 x 4 determinant by 2 x 2 minors). Any failing set of the array is such a
      shift, so none is missed and each is counted once. Work: about C(k-1,3) (column, pair) steps.
      Default: brute when C(k,5) <= 1e9, else fast (argument 4 forces one; threads from CHECK_THREADS, signature rows
      from CHECK_R; CHECK_PROGRESS=FILE resumes by x1 (progress.h); CHECK_LIST=FILE writes every failing set;
      CHECK_TASKS=a:b runs only x1 = a..b, a share of the work whose tallies add up). Memory: a few MB per thread.
   2. Spot check of the covering array it gives, CA(n(q^5 - q) + q; 5, k, q) (row (u0,..,u4) of block r puts
      u0 + u1 x + u2 y + u3 z + u4 w in a column whose point in row r is (x, y, z, w); the q constant rows once):
      for SAMPLES random sets of five columns (default about 2e9 symbol evaluations' worth, 20 to 500), every one of
      the q^5 tuples of symbols must appear.
   cc -O3 -o scphf5_fast scphf5_fast.c -lpthread && ./scphf5_fast q FILE [SAMPLES] [brute|fast] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>
#include "progress.h"

#define MAXQ 32
#define MAXN 64
#define MAXK 65535
#define WILD 0xFF
#define RMAX 6

static const char *ARRAY;
static int q, p, m;
static int poly[8];  /* low degree first, monic */
static uint8_t ADD[MAXQ][MAXQ], SUB[MAXQ][MAXQ], MUL[MAXQ][MAXQ], INV[MAXQ];

static int padd(int a, int b) {  /* digit-wise addition mod p */
    int r = 0, pw = 1;
    for (int i = 0; i < m; i++, pw *= p) r += (((a / pw) % p + (b / pw) % p) % p) * pw;
    return r;
}

static int times_x(int a) {  /* a * x, reduced with x^m = -(poly[0] + ... + poly[m-1] x^(m-1)) */
    int d[8], top, pw = 1;
    for (int i = 0; i < m; i++, a /= p) d[i] = a % p;
    top = d[m - 1];
    for (int i = m - 1; i > 0; i--) d[i] = d[i - 1];
    d[0] = 0;
    int r = 0;
    for (int i = 0; i < m; i++, pw *= p) r += (((d[i] - top * poly[i]) % p + p) % p) * pw;
    return r;
}

static int pmul(int a, int b) {  /* Horner over the digits of b, highest first */
    int digits[8], r = 0;
    for (int i = 0; i < m; i++, b /= p) digits[i] = b % p;
    for (int i = m - 1; i >= 0; i--) {
        r = times_x(r);
        for (int j = 0; j < digits[i]; j++) r = padd(r, a);
    }
    return r;
}

static int setup(void) {
    static const struct { int q, p, m, poly[6]; } F[] = {
        {4, 2, 2, {1, 1, 1}}, {8, 2, 3, {1, 1, 0, 1}}, {16, 2, 4, {1, 1, 0, 0, 1}}, {32, 2, 5, {1, 0, 1, 0, 0, 1}},
        {9, 3, 2, {1, 0, 1}}, {27, 3, 3, {1, 2, 0, 1}}, {25, 5, 2, {2, 1, 1}}};
    p = 0;
    for (int i = 0; i < 7; i++)
        if (F[i].q == q) { p = F[i].p; m = F[i].m; memcpy(poly, F[i].poly, sizeof F[i].poly); }
    if (!p) {
        for (int d = 2; d * d <= q; d++) if (q % d == 0) return 0;
        p = q; m = 1;
        for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { ADD[a][b] = (uint8_t)((a + b) % q); MUL[a][b] = (uint8_t)(a * b % q); }
    } else {
        for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { ADD[a][b] = (uint8_t)padd(a, b); MUL[a][b] = (uint8_t)pmul(a, b); }
    }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) if (ADD[b][c] == a) SUB[a][b] = (uint8_t)c;
    for (int a = 1; a < q; a++) {
        int inv = 0;
        for (int b = 1; b < q; b++) if (MUL[a][b] == 1) inv = b;
        if (!inv) return 0;
        INV[a] = (uint8_t)inv;
    }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            if (MUL[a][b] != MUL[b][a] || ADD[a][b] != ADD[b][a]) return 0;
            for (int c = 0; c < q; c++)
                if (MUL[MUL[a][b]][c] != MUL[a][MUL[b][c]] || MUL[a][ADD[b][c]] != ADD[MUL[a][b]][MUL[a][c]] ||
                    ADD[ADD[a][b]][c] != ADD[a][ADD[b][c]]) return 0;
        }
    return 1;
}

static int n, k;
static uint8_t *Xc[MAXN][4];  /* coordinate c of column j's point in row r: Xc[r][c][j] */

static int rank_rows(int rows, uint8_t (*a)[4]) {  /* rank of a rows x 4 matrix over GF(q) (destroyed) */
    int rank = 0;
    for (int c = 0; c < 4 && rank < rows; c++) {
        int piv = -1;
        for (int i = rank; i < rows && piv < 0; i++) if (a[i][c]) piv = i;
        if (piv < 0) continue;
        for (int j = 0; j < 4; j++) { uint8_t t = a[rank][j]; a[rank][j] = a[piv][j]; a[piv][j] = t; }
        int iv = INV[a[rank][c]];
        for (int i = rank + 1; i < rows; i++)
            if (a[i][c]) { int f = MUL[a[i][c]][iv]; for (int j = 0; j < 4; j++) a[i][j] = SUB[a[i][j]][MUL[f][a[rank][j]]]; }
        rank++;
    }
    return rank;
}

static uint8_t *PK[MAXN];  /* PK[r][4 j + c]: coordinate c of column j's point in row r, packed */

static inline int det4_nonzero(const uint8_t *u, const uint8_t *v, const uint8_t *w, const uint8_t *x) {
    /* Laplace expansion along the 2 x 2 minors of the first two rows; no branches */
    int a01 = SUB[MUL[u[0]][v[1]]][MUL[u[1]][v[0]]], a02 = SUB[MUL[u[0]][v[2]]][MUL[u[2]][v[0]]];
    int a03 = SUB[MUL[u[0]][v[3]]][MUL[u[3]][v[0]]], a12 = SUB[MUL[u[1]][v[2]]][MUL[u[2]][v[1]]];
    int a13 = SUB[MUL[u[1]][v[3]]][MUL[u[3]][v[1]]], a23 = SUB[MUL[u[2]][v[3]]][MUL[u[3]][v[2]]];
    int b01 = SUB[MUL[w[0]][x[1]]][MUL[w[1]][x[0]]], b02 = SUB[MUL[w[0]][x[2]]][MUL[w[2]][x[0]]];
    int b03 = SUB[MUL[w[0]][x[3]]][MUL[w[3]][x[0]]], b12 = SUB[MUL[w[1]][x[2]]][MUL[w[2]][x[1]]];
    int b13 = SUB[MUL[w[1]][x[3]]][MUL[w[3]][x[1]]], b23 = SUB[MUL[w[2]][x[3]]][MUL[w[3]][x[2]]];
    int d = SUB[MUL[a01][b23]][MUL[a02][b13]];
    d = ADD[ADD[d][MUL[a03][b12]]][MUL[a12][b03]];
    d = ADD[SUB[d][MUL[a13][b02]]][MUL[a23][b01]];
    return d != 0;
}

static int indep5(int r, const int *s) {  /* columns s[0..4]: five points of row r not on one hyperplane */
    const uint8_t *P = PK[r], *p0 = P + 4 * (size_t)s[0];
    uint8_t d[4][4];
    for (int i = 0; i < 4; i++) {
        const uint8_t *pi = P + 4 * (size_t)s[i + 1];
        for (int c = 0; c < 4; c++) d[i][c] = SUB[pi[c]][p0[c]];
    }
    return det4_nonzero(d[0], d[1], d[2], d[3]);
}

static int affine_shift(int r) {  /* row r is v, Tv, T^2 v, ... for an invertible affine T of AG(4,q) */
    for (int j0 = 0; j0 + 5 < k && j0 < 256; j0++) {
        int A[5][10];  /* rows (1, point j0+i | 1, point j0+i+1): solve V^T X = W^T, X = T^T */
        for (int i = 0; i < 5; i++) {
            A[i][0] = 1; A[i][5] = 1;
            for (int c = 0; c < 4; c++) { A[i][1 + c] = Xc[r][c][j0 + i]; A[i][6 + c] = Xc[r][c][j0 + i + 1]; }
        }
        int ok = 1;
        for (int c = 0; c < 5 && ok; c++) {
            int piv = -1;
            for (int i = c; i < 5 && piv < 0; i++) if (A[i][c]) piv = i;
            if (piv < 0) { ok = 0; break; }
            for (int j = 0; j < 10; j++) { int t = A[c][j]; A[c][j] = A[piv][j]; A[piv][j] = t; }
            int iv = INV[A[c][c]];
            for (int j = 0; j < 10; j++) A[c][j] = MUL[A[c][j]][iv];
            for (int i = 0; i < 5; i++)
                if (i != c && A[i][c]) { int f = A[i][c]; for (int j = 0; j < 10; j++) A[i][j] = SUB[A[i][j]][MUL[f][A[c][j]]]; }
        }
        if (!ok) continue;  /* these five points lie on a hyperplane: next window */
        int Tt[5][5];
        uint8_t E[4][4];
        for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) Tt[i][j] = A[i][5 + j];
        if (Tt[0][0] != 1 || Tt[1][0] || Tt[2][0] || Tt[3][0] || Tt[4][0]) return 0;  /* not affine */
        for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) E[i][j] = (uint8_t)Tt[1 + j][1 + i];  /* linear part */
        if (rank_rows(4, E) < 4) return 0;  /* T not invertible */
        for (int j = 0; j + 1 < k; j++) {  /* (T h)_i = sum_l Tt[l][i] h_l with h = (1, point j) */
            int h[5] = {1, Xc[r][0][j], Xc[r][1][j], Xc[r][2][j], Xc[r][3][j]};
            for (int i = 0; i < 5; i++) {
                int v = 0;
                for (int l = 0; l < 5; l++) v = ADD[v][MUL[Tt[l][i]][h[l]]];
                if (v != (i ? Xc[r][i - 1][j + 1] : 1)) return 0;
            }
        }
        return 1;
    }
    return 0;
}

/* ---------- fast method ---------- */
static int ncyc, crow[MAXN], noth, orow[MAXN];
static uint8_t *UD[MAXN];          /* UD[i][4 x + c]: coordinate c of column x's point minus column 0's, row crow[i] */
static int NP, ZID, LW;            /* points of PG(2,q), id of the zero vector, LINE row width */
static uint16_t *PTID;             /* (a q + b) q + c -> point id of (a, b, c), ZID for zero */
static uint8_t *LINE;              /* LINE[P * LW + Q]: line PQ among the q + 1 lines through P; WILD for Q = P or Z */
static int RFIX, NTH, TFROM = 1, TTO = MAXK;  /* x1 tasks run: TFROM..TTO (CHECK_TASKS) */
static FILE *LIST;
static pthread_mutex_t LMX = PTHREAD_MUTEX_INITIALIZER;

static int normalize3(int *v) {  /* scale so the first nonzero coordinate is 1; 0 if zero */
    int l = 0;
    while (l < 3 && !v[l]) l++;
    if (l == 3) return 0;
    int iv = INV[v[l]];
    for (int i = 0; i < 3; i++) v[i] = MUL[v[i]][iv];
    return 1;
}

static void make_plane(void) {  /* points of PG(2,q) (first nonzero coordinate 1) and the line table */
    NP = q * q + q + 1;
    ZID = NP;
    LW = NP + 1;
    int (*pts)[3] = malloc(sizeof *pts * NP), np = 0;
    PTID = malloc(sizeof(uint16_t) * q * q * q);
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++) {
                int v[3] = {a, b, c};
                if (!normalize3(v)) { PTID[(a * q + b) * q + c] = (uint16_t)ZID; continue; }
                if (v[0] == a && v[1] == b && v[2] == c) { pts[np][0] = a; pts[np][1] = b; pts[np][2] = c; np++; }
            }
    if (np != NP) { fprintf(stderr, "wrong number of points of PG(2,q)\n"); exit(2); }
    for (int a = 0; a < q; a++)  /* every vector -> its point */
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++) {
                int v[3] = {a, b, c};
                if (!normalize3(v)) continue;
                int id = -1;
                for (int i = 0; i < NP && id < 0; i++) if (pts[i][0] == v[0] && pts[i][1] == v[1] && pts[i][2] == v[2]) id = i;
                PTID[(a * q + b) * q + c] = (uint16_t)id;
            }
    /* lines have the same coordinates (normals); local index of each line through P by increasing id */
    int *loc = malloc(sizeof(int) * NP * NP);
    for (int P = 0; P < NP; P++) {
        int cnt = 0;
        for (int L = 0; L < NP; L++) {
            int d = ADD[ADD[MUL[pts[P][0]][pts[L][0]]][MUL[pts[P][1]][pts[L][1]]]][MUL[pts[P][2]][pts[L][2]]];
            loc[P * NP + L] = d ? -1 : cnt++;
        }
        if (cnt != q + 1) { fprintf(stderr, "wrong number of lines through a point\n"); exit(2); }
    }
    LINE = malloc((size_t)LW * LW);
    memset(LINE, WILD, (size_t)LW * LW);
    for (int P = 0; P < NP; P++)
        for (int Q = 0; Q < NP; Q++) {
            if (Q == P) continue;
            const int *a = pts[P], *b = pts[Q];
            int v[3] = {SUB[MUL[a[1]][b[2]]][MUL[a[2]][b[1]]], SUB[MUL[a[2]][b[0]]][MUL[a[0]][b[2]]],
                        SUB[MUL[a[0]][b[1]]][MUL[a[1]][b[0]]]};
            if (!normalize3(v)) { fprintf(stderr, "distinct points with a zero cross product\n"); exit(2); }
            int L = PTID[(v[0] * q + v[1]) * q + v[2]];
            if (loc[P * NP + L] < 0 || loc[Q * NP + L] < 0) { fprintf(stderr, "line misses its points\n"); exit(2); }
            LINE[P * LW + Q] = (uint8_t)loc[P * NP + L];
        }
    free(loc);
    free(pts);
}

struct th {
    uint16_t *pt;                  /* pt[i k + x]: point of u(x) modulo <u(x1)> (ZID: zero) */
    uint32_t *head;                /* direct table, index = signature: stamp 16 | last column 16 */
    uint16_t *nxt;                 /* earlier column with the same signature (END: none) */
    unsigned stamp;
    uint32_t *sig;                 /* level 0: signature of each column */
    uint8_t *wf;                   /* level 0: bit j set when the column is wild in signature row j */
    uint64_t *cand;                /* candidate pairs: first row still to test << 32 | y << 16 | x */
    int ncand, ccap;
    int *lst[MAXN + 2];            /* column lists per level (wild columns of the level above) */
    int *hv;                       /* level 0: columns wild in three or more signature rows */
    uint16_t *cnt;                 /* cnt[i LW + P]: columns after x2 with point P in cyclic row i */
    uint8_t *mark;
    long long units, cands, base, shifted, bad;
    int first[5], tfirst[5];       /* smallest failing set over all tasks, and in the current task */
    /* current pair */
    int nl, x1, x2;
    int lp[MAXN];                  /* point P of each row of the pair */
    const uint8_t *LR[MAXN];       /* its LINE row */
    const uint16_t *PP[MAXN];
    uint8_t *cl[RMAX];             /* level 0: class of each column in signature row j */
};

#define END 0xFFFF
static size_t DSZ;                 /* entries of the direct table */
static int LWP;                    /* LINE row stride (LW rounded up to 64, padded with WILD) */

static inline unsigned cls(const struct th *T, int j, int x) { return T->LR[j][T->PP[j][x]]; }

static inline int compat_rest(const struct th *T, int y, int x, int from) {  /* classes agree or one is wild in
                                                                                rows from.. of the pair */
    const uint8_t *const *LR = T->LR;
    const uint16_t *const *PP = T->PP;
    for (int j = from, nl = T->nl; j < nl; j++) {
        unsigned cy = LR[j][PP[j][y]], cx = LR[j][PP[j][x]];
        if (cy != cx && cy != WILD && cx != WILD) return 0;
    }
    return 1;
}

static void lex_first(int *best, const int *s) {
    if (best[0] < 0) { memcpy(best, s, sizeof(int) * 5); return; }
    for (int i = 0; i < 5; i++) if (s[i] != best[i]) { if (s[i] < best[i]) memcpy(best, s, sizeof(int) * 5); return; }
}

static void failing_base(struct th *T, int y, int x) {  /* {0, x1, x2, y, x} fails in every cyclic row */
    int s[5] = {0, T->x1, T->x2, y < x ? y : x, y < x ? x : y};
    for (int i = 0; i < ncyc; i++) {  /* confirmation by Gaussian elimination, apart from the class tables */
        uint8_t a[4][4];
        for (int j = 0; j < 4; j++) memcpy(a[j], UD[i] + 4 * (size_t)s[j + 1], 4);
        if (rank_rows(4, a) == 4) {
            fprintf(stderr, "internal disagreement: %d %d %d %d %d independent in row %d\n", s[0], s[1], s[2], s[3], s[4], crow[i]);
            exit(3);
        }
    }
    T->base++;
    for (int sh = 0; sh + s[4] < k; sh++) {
        int t5[5], ok = 0;
        for (int i = 0; i < 5; i++) t5[i] = s[i] + sh;
        for (int o = 0; o < noth && !ok; o++) ok = indep5(orow[o], t5);
        T->shifted++;
        if (!ok) {
            T->bad++;
            lex_first(T->first, t5);
            lex_first(T->tfirst, t5);
            if (LIST) { pthread_mutex_lock(&LMX); fprintf(LIST, "%d %d %d %d %d\n", t5[0], t5[1], t5[2], t5[3], t5[4]); pthread_mutex_unlock(&LMX); }
        }
    }
}

static void flush_cands(struct th *T) {
    for (int c = 0; c < T->ncand; c++) {
        uint64_t e = T->cand[c];
        int y = (int)(e >> 16 & 0xFFFF), x = (int)(e & 0xFFFF), from = (int)(e >> 32);
        if (compat_rest(T, y, x, from)) failing_base(T, y, x);
    }
    T->cands += T->ncand;
    T->ncand = 0;
}

static inline void add_cand(struct th *T, int y, int x, int from) {
    if (T->ncand == T->ccap) flush_cands(T);
    T->cand[T->ncand++] = (uint64_t)from << 32 | (uint64_t)y << 16 | (uint64_t)x;
}

static void new_stamp(struct th *T) {
    if (++T->stamp == 0x10000) { memset(T->head, 0, sizeof(uint32_t) * (DSZ + 1)); T->stamp = 1; }
}

static int pick_rows(int ncols, int avail) {  /* signature rows: (q+1)^m >= 4 ncols, table size and rows allowing */
    int mr = 1;
    double d = q + 1;
    if (RFIX) mr = RFIX, d = 0;
    else while (mr < RMAX && d < 4.0 * ncols && d * (q + 1) <= (double)DSZ) { mr++; d *= q + 1; }
    while (mr > 1) {  /* a fixed R must still fit the table */
        double t = 1;
        for (int j = 0; j < mr; j++) t *= q + 1;
        if (t <= (double)DSZ) break;
        mr--;
    }
    if (mr > avail) mr = avail;
    return mr;
}

static inline void chain_insert(struct th *T, uint32_t s, int x, int from) {  /* x after every column with
                                                                                 signature s: those pairs are candidates */
    uint32_t e = T->head[s];
    int y = (e >> 16) == T->stamp ? (int)(e & 0xFFFF) : END;
    T->nxt[x] = (uint16_t)y;
    for (; y != END; y = T->nxt[y]) add_cand(T, y, x, from);
    T->head[s] = T->stamp << 16 | (uint32_t)x;
}

static inline void chain_probe(struct th *T, uint32_t s, int x, int from) {
    uint32_t e = T->head[s];
    if ((e >> 16) != T->stamp) return;
    for (int y = (int)(e & 0xFFFF); y != END; y = T->nxt[y]) add_cand(T, y, x, from);
}

static void probe_wild(struct th *T, int x, const unsigned *dig, unsigned wm, int mr, int from) {
    /* x wild in one or two of the mr signature rows: every signature it matches */
    uint32_t B = (uint32_t)q + 1, pw[RMAX + 1], base = 0;
    int wr[2], nw = 0;
    pw[0] = 1;
    for (int j = 1; j <= mr; j++) pw[j] = pw[j - 1] * B;
    for (int j = 0; j < mr; j++) { if (wm >> j & 1) wr[nw++] = j; else base += dig[j] * pw[j]; }
    if (nw == 1) for (uint32_t a = 0; a < B; a++) chain_probe(T, base + a * pw[wr[0]], x, from);
    else for (uint32_t a = 0; a < B; a++) for (uint32_t b = 0; b < B; b++) chain_probe(T, base + a * pw[wr[0]] + b * pw[wr[1]], x, from);
}

static void level(struct th *T, const int *C, int nc, int ro, int depth) {
    /* pairs of columns in C (all wild in some signature row of every level above) that agree in every row: the next
       block of rows, from ro, is the signature; wild columns again go one level down; no rows left: every pair */
    if (nc < 2) return;
    int avail = T->nl - ro;
    if (avail <= 0 || nc <= 4) {  /* few columns or no rows left: every pair, tested in every row */
        for (int a = 0; a < nc; a++) for (int b = a + 1; b < nc; b++) add_cand(T, C[a] < C[b] ? C[a] : C[b], C[a] < C[b] ? C[b] : C[a], 0);
        return;
    }
    int mr = pick_rows(nc, avail), nw = 0, nh = 0;
    if (!T->lst[depth]) T->lst[depth] = malloc(sizeof(int) * ((size_t)k + 1));
    int *W = T->lst[depth], *H = T->lst[depth] + nc;  /* wild columns from the front, heavy from the back */
    unsigned dg[RMAX];
    new_stamp(T);
    for (int a = 0; a < nc; a++) {
        int x = C[a];
        unsigned wm = 0, nwr = 0;
        uint32_t s = 0;
        for (int j = mr - 1; j >= 0; j--) {
            unsigned c = cls(T, ro + j, x);
            if (c == WILD) { wm |= 1u << j; nwr++; c = 0; }
            s = s * ((uint32_t)q + 1) + c;
        }
        if (!wm) chain_insert(T, s, x, 0);
        else if (nwr <= 2) W[nw++] = x;
        else H[-(++nh)] = x;
    }
    for (int a = 0; a < nw; a++) {
        int x = W[a];
        unsigned wm = 0;
        for (int j = 0; j < mr; j++) { dg[j] = cls(T, ro + j, x); if (dg[j] == WILD) wm |= 1u << j; }
        probe_wild(T, x, dg, wm, mr, 0);
    }
    for (int a = 1; a <= nh; a++) T->mark[H[-a]] = 1;
    for (int a = 1; a <= nh; a++) {  /* wild in three or more signature rows: with every column of C */
        int x = H[-a];
        for (int b = 0; b < nc; b++) {
            int y = C[b];
            if (y == x || (T->mark[y] && y < x)) continue;
            add_cand(T, y < x ? y : x, y < x ? x : y, 0);
        }
    }
    for (int a = 1; a <= nh; a++) T->mark[H[-a]] = 0;
    level(T, W, nw, ro + mr, depth + 1);
}

#if defined(__ARM_NEON)
#include <arm_neon.h>
static void sigs_neon(struct th *T, int mr, int x0) {  /* level 0: signature and wild flag of columns x0..k-1, 16 at
                                                          a time with table lookups (LW <= 512) */
    int nseg = (LW + 63) / 64;
    uint16_t B = (uint16_t)(q + 1);
    int wide = 1;
    for (int j = 0; j < mr; j++) wide *= q + 1;
    wide = wide > 65536;
    uint8x16_t v64 = vdupq_n_u8(64), v128 = vdupq_n_u8(128), v192 = vdupq_n_u8(192), vff = vdupq_n_u8(WILD);
    uint32_t *sg = T->sig;
    uint16_t *sg16 = (uint16_t *)T->sig;
    for (int j = mr - 1; j >= 0; j--) {
        const uint8_t *tb = LINE + (size_t)T->lp[j] * LWP;
        uint8x16x4_t s0 = vld1q_u8_x4(tb), s1 = s0, s2 = s0, s3 = s0, s4 = s0, s5 = s0, s6 = s0, s7 = s0;
        if (nseg > 1) s1 = vld1q_u8_x4(tb + 64);
        if (nseg > 2) s2 = vld1q_u8_x4(tb + 128);
        if (nseg > 3) s3 = vld1q_u8_x4(tb + 192);
        if (nseg > 4) s4 = vld1q_u8_x4(tb + 256);
        if (nseg > 5) s5 = vld1q_u8_x4(tb + 320);
        if (nseg > 6) s6 = vld1q_u8_x4(tb + 384);
        if (nseg > 7) s7 = vld1q_u8_x4(tb + 448);
        const uint16_t *pp = T->PP[j];
        for (int x = x0; x < k; x += 16) {
            uint8x16_t ia = vreinterpretq_u8_u16(vld1q_u16(pp + x)), ib = vreinterpretq_u8_u16(vld1q_u16(pp + x + 8));
            uint8x16_t lo = vuzp1q_u8(ia, ib), c = vqtbl4q_u8(s0, lo);
            if (nseg > 1) c = vqtbx4q_u8(c, s1, vsubq_u8(lo, v64));
            if (nseg > 2) c = vqtbx4q_u8(c, s2, vsubq_u8(lo, v128));
            if (nseg > 3) c = vqtbx4q_u8(c, s3, vsubq_u8(lo, v192));
            if (nseg > 4) {
                uint8x16_t hi = vuzp2q_u8(ia, ib), ch = vqtbl4q_u8(s4, lo);
                if (nseg > 5) ch = vqtbx4q_u8(ch, s5, vsubq_u8(lo, v64));
                if (nseg > 6) ch = vqtbx4q_u8(ch, s6, vsubq_u8(lo, v128));
                if (nseg > 7) ch = vqtbx4q_u8(ch, s7, vsubq_u8(lo, v192));
                c = vbslq_u8(vtstq_u8(hi, hi), ch, c);
            }
            vst1q_u8(T->cl[j] + x, c);
            uint8x16_t w = vandq_u8(vceqq_u8(c, vff), vdupq_n_u8((uint8_t)(1u << j)));  /* bit j: wild in row j */
            if (j < mr - 1) w = vorrq_u8(w, vld1q_u8(T->wf + x));
            vst1q_u8(T->wf + x, w);
            uint16x8_t cl = vmovl_u8(vget_low_u8(c)), ch16 = vmovl_high_u8(c);
            if (!wide) {
                uint16x8_t a = cl, b = ch16;
                if (j < mr - 1) { a = vmlaq_n_u16(cl, vld1q_u16(sg16 + x), B); b = vmlaq_n_u16(ch16, vld1q_u16(sg16 + x + 8), B); }
                vst1q_u16(sg16 + x, a);
                vst1q_u16(sg16 + x + 8, b);
            } else {
                uint32x4_t c0 = vmovl_u16(vget_low_u16(cl)), c1 = vmovl_high_u16(cl), c2 = vmovl_u16(vget_low_u16(ch16)), c3 = vmovl_high_u16(ch16);
                if (j < mr - 1) {
                    c0 = vmlaq_n_u32(c0, vld1q_u32(sg + x), B); c1 = vmlaq_n_u32(c1, vld1q_u32(sg + x + 4), B);
                    c2 = vmlaq_n_u32(c2, vld1q_u32(sg + x + 8), B); c3 = vmlaq_n_u32(c3, vld1q_u32(sg + x + 12), B);
                }
                vst1q_u32(sg + x, c0); vst1q_u32(sg + x + 4, c1); vst1q_u32(sg + x + 8, c2); vst1q_u32(sg + x + 12, c3);
            }
        }
    }
}
#endif

static void pair(struct th *T, const int *l2, int L2) {  /* columns x1 < x2 fixed: the pairs after x2 */
    int x2 = T->x2, nl = 0, wc[MAXN];
    for (int j = 0; j < L2; j++) {
        const uint16_t *pt = T->pt + (size_t)l2[j] * k;
        int P = pt[x2];
        if (P == ZID) continue;  /* u(x1), u(x2) dependent: the row fails for every completion */
        const uint16_t *cn = T->cnt + (size_t)l2[j] * LW;
        wc[nl] = cn[P] + cn[ZID];  /* columns wild in this row */
        T->lp[nl] = P;
        T->PP[nl] = pt;
        nl++;
    }
    T->nl = nl;
    int kk = k - 1 - x2, x0 = x2 + 1;
    T->units += kk;
    if (nl == 0) {  /* no row left: every pair fails in the cyclic rows */
        for (int y = x0; y < k; y++) for (int x = y + 1; x < k; x++) failing_base(T, y, x);
        return;
    }
    int mr = pick_rows(kk, nl), nw = 0, nh = 0, wide = 1;
    for (int a = 0; a < mr; a++) {  /* signature rows: the fewest wild columns first; then the most wild of them in
                                       digit 0, so its q + 1 probes are adjacent */
        int b = a;
        for (int c = a + 1; c < nl; c++) if (wc[c] < wc[b]) b = c;
        int t = wc[a]; wc[a] = wc[b]; wc[b] = t;
        t = T->lp[a]; T->lp[a] = T->lp[b]; T->lp[b] = t;
        const uint16_t *tp = T->PP[a]; T->PP[a] = T->PP[b]; T->PP[b] = tp;
    }
    {
        int b = 0;
        for (int c = 1; c < mr; c++) if (wc[c] > wc[b]) b = c;
        int t = T->lp[0]; T->lp[0] = T->lp[b]; T->lp[b] = t;
        const uint16_t *tp = T->PP[0]; T->PP[0] = T->PP[b]; T->PP[b] = tp;
    }
    for (int j = 0; j < nl; j++) T->LR[j] = LINE + (size_t)T->lp[j] * LWP;
    for (int j = 0; j < mr; j++) wide *= q + 1;
    wide = wide > 65536;
    if (!T->lst[0]) T->lst[0] = malloc(sizeof(int) * ((size_t)k + 1));
    int *W = T->lst[0], *H = T->hv + kk;  /* H[-1], H[-2], ... */
    new_stamp(T);
#if defined(__ARM_NEON)
    int neon = LW <= 512;
    if (neon) sigs_neon(T, mr, x0);
#else
    int neon = 0;
#endif
    const uint16_t *sg16 = (const uint16_t *)T->sig;
    int *Mc = T->lst[MAXN + 1], nm = 0;  /* columns with an earlier column of the same signature */
    if (!neon)
        for (int x = x0; x < k; x++) {  /* signatures one column at a time */
            unsigned w = 0;
            uint32_t sv = 0;
            for (int j = mr - 1; j >= 0; j--) {
                unsigned c = cls(T, j, x);
                T->cl[j][x] = (uint8_t)c;
                w = w << 1 | (c == WILD);
                sv = sv * ((uint32_t)q + 1) + (c == WILD ? 0 : c);
            }
            T->wf[x] = (uint8_t)w;
            T->sig[x] = sv;
        }
    uint32_t *head = T->head, stamp = T->stamp, dummy = (uint32_t)DSZ;  /* wild columns write the spare entry */
    uint16_t *nxt = T->nxt;
    for (int x = x0; x < k; x++) {  /* no branch per column: collisions and wild columns are listed */
        uint32_t sv = neon && !wide ? sg16[x] : T->sig[x];
        unsigned w = T->wf[x];
        sv = w ? dummy : sv;
        uint32_t e = head[sv];
        unsigned valid = ((e >> 16) == stamp) & (w == 0);
        nxt[x] = valid ? (uint16_t)(e & 0xFFFF) : (uint16_t)END;
        head[sv] = stamp << 16 | (uint32_t)x;
        Mc[nm] = x; nm += (int)valid;
        W[nw] = x; nw += w != 0;
    }
    for (int a = 0; a < nm; a++) {  /* same signature: candidates, tested in the other rows */
        int x = Mc[a];
        for (int y = nxt[x]; y != END; y = nxt[y]) add_cand(T, y, x, mr);
    }
    { /* columns wild in three or more signature rows leave the wild list */
        int keep = 0;
        for (int a = 0; a < nw; a++) {
            int x = W[a];
            if (__builtin_popcount(T->wf[x]) <= 2) W[keep++] = x; else H[-(++nh)] = x;
        }
        nw = keep;
    }
    {   /* wild columns, against every column entered: every signature each one matches */
        uint32_t pw[RMAX + 1], B = (uint32_t)q + 1;
        pw[0] = 1;
        for (int j = 1; j <= mr; j++) pw[j] = pw[j - 1] * B;
        for (int a = 0; a < nw; a++) {
            int x = W[a];
            unsigned wm = T->wf[x];
            uint32_t base = 0, st0 = 0, st1 = 0;
            int nwr = 0;
            for (int j = 0; j < mr; j++) {
                if (wm >> j & 1) { if (nwr++) st1 = pw[j]; else st0 = pw[j]; }
                else base += T->cl[j][x] * pw[j];
            }
            if (nwr == 1) {
                for (uint32_t i = 0, ix = base; i < B; i++, ix += st0) {
                    uint32_t e = head[ix];
                    if ((e >> 16) == stamp) for (int y = (int)(e & 0xFFFF); y != END; y = nxt[y]) add_cand(T, y, x, mr);
                }
            } else {
                for (uint32_t i = 0; i < B; i++)
                    for (uint32_t i2 = 0, ix = base + i * st0; i2 < B; i2++, ix += st1) {
                        uint32_t e = head[ix];
                        if ((e >> 16) == stamp) for (int y = (int)(e & 0xFFFF); y != END; y = nxt[y]) add_cand(T, y, x, mr);
                    }
            }
        }
    }
    for (int a = 1; a <= nh; a++) T->mark[H[-a]] = 1;
    for (int a = 1; a <= nh; a++) {  /* wild in three or more signature rows: with every column */
        int x = H[-a];
        for (int y = x0; y < k; y++) {
            if (y == x || (T->mark[y] && y < x)) continue;
            add_cand(T, y < x ? y : x, y < x ? x : y, 0);
        }
    }
    for (int a = 1; a <= nh; a++) T->mark[H[-a]] = 0;
    level(T, W, nw, mr, 1);  /* pairs of wild columns: the next rows */
    flush_cands(T);
}

static int nexttask;
static struct th *TH;

static void do_x1(struct th *T, int x1) {
    int l2[MAXN], L2 = 0;
    T->x1 = x1;
    for (int i = 0; i < ncyc; i++) {
        const uint8_t *u1 = UD[i] + 4 * (size_t)x1;
        int a = -1;
        for (int c = 0; c < 4 && a < 0; c++) if (u1[c]) a = c;
        if (a < 0) continue;  /* column x1 on column 0's point: the row fails for every set with both */
        int iv = INV[u1[a]], f[3], nf = 0;
        for (int c = 0; c < 4; c++) if (c != a) f[nf++] = c;
        const uint8_t *M0 = MUL[MUL[u1[f[0]]][iv]], *M1 = MUL[MUL[u1[f[1]]][iv]], *M2 = MUL[MUL[u1[f[2]]][iv]];
        uint16_t *pt = T->pt + (size_t)i * k;
        int f0 = f[0], f1 = f[1], f2 = f[2], qq = q;
        for (int x = x1 + 1; x < k; x++) {  /* u(x) modulo u(x1): the three coordinates left, as a point */
            const uint8_t *v = UD[i] + 4 * (size_t)x;
            int g = v[a];
            int a0 = SUB[v[f0]][M0[g]], a1 = SUB[v[f1]][M1[g]], a2 = SUB[v[f2]][M2[g]];
            pt[x] = PTID[(a0 * qq + a1) * qq + a2];
        }
        uint16_t *cn = T->cnt + (size_t)i * LW;
        memset(cn, 0, sizeof(uint16_t) * LW);
        for (int x = x1 + 1; x < k; x++) cn[pt[x]]++;
        l2[L2++] = i;
    }
    for (int x2 = x1 + 1; x2 + 2 < k; x2++) {
        for (int j = 0; j < L2; j++) T->cnt[(size_t)l2[j] * LW + T->pt[(size_t)l2[j] * k + x2]]--;  /* x2 leaves */
        T->x2 = x2;
        pair(T, l2, L2);
    }
}

static void *worker(void *arg) {
    struct th *T = arg;
    for (;;) {
        int x1 = __sync_fetch_and_add(&nexttask, 1) + TFROM;
        if (x1 + 3 >= k || x1 > TTO) return NULL;
        if (PDONE && PDONE[x1]) continue;  /* finished by an earlier run (CHECK_PROGRESS) */
        long long u0 = T->units, b0 = T->bad, a0 = T->base, h0 = T->shifted;
        T->tfirst[0] = -1;
        do_x1(T, x1);
        progress_line(x1, T->units - u0, T->bad - b0, T->base - a0, T->shifted - h0, T->tfirst[0] >= 0 ? T->tfirst : NULL, 5);
    }
}

static void resumed_first(int *first) {  /* smallest failing set over the tasks taken from CHECK_PROGRESS (progress.h
                                            keeps only the first line's) */
    const char *pf = getenv("CHECK_PROGRESS");
    char line[512];
    if (!PRESUMED || !pf) return;
    FILE *in = fopen(pf, "r");
    if (!in) return;
    if (fgets(line, sizeof line, in))
        while (fgets(line, sizeof line, in)) {
            int i, f[5], used = 0, ok = 1;
            long long a, b, c, d;
            if (sscanf(line, "%d %lld %lld %lld %lld%n", &i, &a, &b, &c, &d, &used) != 5) break;
            for (int x = 0; x < 5 && ok; x++) { int u = 0; ok = sscanf(line + used, "%d%n", &f[x], &u) == 1; used += u; }
            if (ok && f[0] >= 0) lex_first(first, f);
        }
    fclose(in);
}

static void fast_check(long long *units, long long *bad, int first[5], long long *base, long long *shifted, long long *cands) {
    make_plane();
    for (int i = 0; i < ncyc; i++) {
        UD[i] = malloc(4 * (size_t)k);
        int r = crow[i];
        for (int x = 0; x < k; x++) for (int c = 0; c < 4; c++) UD[i][4 * (size_t)x + c] = SUB[Xc[r][c][x]][Xc[r][c][0]];
    }
    progress_open(ARRAY, 5, q, -1, k, 5);
    LWP = (LW + 63) / 64 * 64;
    { /* LINE with rows padded to a multiple of 64 bytes (WILD), for the table lookups */
        uint8_t *pad = malloc((size_t)LW * LWP + 64);
        memset(pad, WILD, (size_t)LW * LWP + 64);
        for (int P = 0; P < LW; P++) memcpy(pad + (size_t)P * LWP, LINE + (size_t)P * LW, LW);
        free(LINE);
        LINE = pad;
    }
    DSZ = 1;  /* the largest signature space used: (q+1)^m >= 4k, at most 2^20 entries */
    while (DSZ * (q + 1) <= ((size_t)1 << 20) && DSZ < 4 * (size_t)k) DSZ *= q + 1;
    if (DSZ < (size_t)(q + 1) * (q + 1)) DSZ = (size_t)(q + 1) * (q + 1);
    TH = calloc(NTH, sizeof *TH);
    pthread_t th[64];
    for (int w = 0; w < NTH; w++) {
        struct th *T = &TH[w];
        T->pt = calloc((size_t)ncyc * k + 32, sizeof(uint16_t));
        T->head = calloc(DSZ + 1, sizeof(uint32_t));
        T->lst[MAXN + 1] = malloc(sizeof(int) * ((size_t)k + 1));
        T->hv = malloc(sizeof(int) * ((size_t)k + 1));
        T->cnt = malloc(sizeof(uint16_t) * (size_t)ncyc * LW);
        for (int j = 0; j < RMAX; j++) T->cl[j] = malloc((size_t)k + 32);
        T->nxt = malloc(sizeof(uint16_t) * ((size_t)k + 32));
        T->sig = malloc(sizeof(uint32_t) * ((size_t)k + 32));
        T->wf = malloc((size_t)k + 32);
        T->ccap = 4096;
        T->cand = malloc(sizeof(uint64_t) * T->ccap);
        T->mark = calloc((size_t)k + 1, 1);
        T->first[0] = -1;
        pthread_create(&th[w], NULL, worker, T);
    }
    *units = *bad = *base = *shifted = *cands = 0;
    first[0] = -1;
    for (int w = 0; w < NTH; w++) {
        pthread_join(th[w], NULL);
        *units += TH[w].units; *bad += TH[w].bad; *base += TH[w].base; *shifted += TH[w].shifted; *cands += TH[w].cands;
        if (TH[w].first[0] >= 0) lex_first(first, TH[w].first);
    }
    *units += PSETS; *bad += PBAD; *base += PBASE; *shifted += PSHIFT;
    if (PBAD) resumed_first(first);
    if (PRESUMED) printf("resumed: %d tasks (x1) were finished by an earlier run (CHECK_PROGRESS) and their tallies added\n", PRESUMED);
}

static double choose5(double v) { return v < 5 ? 0 : v * (v - 1) * (v - 2) * (v - 3) * (v - 4) / 120; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: scphf5_fast q FILE [SAMPLES] [brute|fast]\n"); return 2; }
    q = atoi(argv[1]);
    if (q < 2 || q > MAXQ || !setup()) { fprintf(stderr, "q is not a supported field order\n"); return 2; }
    ARRAY = argv[2];
    FILE *f = fopen(argv[2], "r");
    if (!f) { perror(argv[2]); return 2; }
    static char line[1 << 24];
    long Q4 = (long)q * q * q * q;
    k = -1;
    while (fgets(line, sizeof line, f)) {
        if (line[0] < '0' || line[0] > '9') continue;
        if (n == MAXN) { fprintf(stderr, "too many rows\n"); return 2; }
        int c = 0;
        for (int i = 0; i < 4; i++) Xc[n][i] = malloc(MAXK);
        for (char *s = strtok(line, " \t\n"); s; s = strtok(NULL, " \t\n")) {
            char *end;
            long id = strtol(s, &end, 10);
            if (*end || id < 0 || id >= Q4 || c == MAXK) { fprintf(stderr, "bad point id or too many columns\n"); return 2; }
            for (int i = 3; i >= 0; i--) { Xc[n][i][c] = (uint8_t)(id % q); id /= q; }
            c++;
        }
        if (k >= 0 && c != k) { fprintf(stderr, "rows differ in length\n"); return 2; }
        k = c; n++;
    }
    fclose(f);
    if (n < 1 || k < 5) { fprintf(stderr, "no array\n"); return 2; }
    for (int r = 0; r < n; r++) {
        PK[r] = malloc(4 * (size_t)k);
        for (int j = 0; j < k; j++) for (int c = 0; c < 4; c++) PK[r][4 * (size_t)j + c] = Xc[r][c][j];
    }
    NTH = (int)sysconf(_SC_NPROCESSORS_ONLN);
    if (getenv("CHECK_THREADS")) NTH = atoi(getenv("CHECK_THREADS"));
    if (NTH < 1) NTH = 1;
    if (NTH > 64) NTH = 64;
    if (getenv("CHECK_R")) RFIX = atoi(getenv("CHECK_R"));
    if (getenv("CHECK_TASKS") && *getenv("CHECK_TASKS")) {  /* a share of the work: x1 in a..b (sum the tallies) */
        if (sscanf(getenv("CHECK_TASKS"), "%d:%d", &TFROM, &TTO) != 2 || TFROM < 1 || TTO < TFROM) { fprintf(stderr, "CHECK_TASKS is a:b\n"); return 2; }
    }
    if (RFIX < 0 || RFIX > RMAX) RFIX = 0;
    if (getenv("CHECK_LIST") && *getenv("CHECK_LIST")) {
        LIST = fopen(getenv("CHECK_LIST"), "w");
        if (!LIST) { perror(getenv("CHECK_LIST")); return 2; }
    }
    for (int r = 0; r < n; r++) { if (affine_shift(r)) crow[ncyc++] = r; else orow[noth++] = r; }
    const char *method = argc > 4 ? argv[4] : choose5(k) <= 1e9 ? "brute" : "fast";
    long long sets = 0, bad = 0, base = 0, shifted = 0, cands = 0;
    int fs[5] = {-1, -1, -1, -1, -1};
    if (!strcmp(method, "fast")) {
        if (!ncyc) { fprintf(stderr, "no row is an affine progression\n"); return 2; }
        fast_check(&sets, &bad, fs, &base, &shifted, &cands);
        printf("fast method: %d rows are affine progressions v, Tv, T^2 v, ... (T invertible), so a set of five columns fails "
               "in all of them exactly when its shift to column 0 does; for every two columns x1 < x2 after column 0 the "
               "later columns were classed by the hyperplanes through column 0, x1, x2 in each such row (signatures of up to "
               "%d rows), %d threads; %lld candidate pairs tested in the other rows; %lld sets holding column 0 fail in "
               "every such row, and their %lld shifts were tested in the other %d rows\n",
               ncyc, RMAX, NTH, cands, base, shifted, noth);
    } else if (!strcmp(method, "brute")) {
        int s[5];
        for (s[0] = 0; s[0] < k; s[0]++)
            for (s[1] = s[0] + 1; s[1] < k; s[1]++)
                for (s[2] = s[1] + 1; s[2] < k; s[2]++)
                    for (s[3] = s[2] + 1; s[3] < k; s[3]++)
                        for (s[4] = s[3] + 1; s[4] < k; s[4]++) {
                            int ok = 0;
                            for (int r = 0; r < n && !ok; r++) ok = indep5(r, s);
                            sets++;
                            if (!ok) {
                                if (!bad) memcpy(fs, s, sizeof s);
                                bad++;
                                if (LIST) fprintf(LIST, "%d %d %d %d %d\n", s[0], s[1], s[2], s[3], s[4]);
                            }
                        }
    } else { fprintf(stderr, "method is brute or fast\n"); return 2; }
    if (LIST) fclose(LIST);
    printf("SCPHF(%d; %d, %d^4, 5): %lld %s, %lld always on one hyperplane", n, k, q, sets,
           !strcmp(method, "brute") ? "sets of five columns checked"
           : "(set of three columns after column 0, later column) steps (every set of five columns is a shift of one holding column 0)", bad);
    if (bad) printf(" (first: columns %d, %d, %d, %d, %d)", fs[0], fs[1], fs[2], fs[3], fs[4]);
    printf("\n");
    /* 2. covering-array spot check */
    long Q5 = Q4 * q, N = (long)n * (Q5 - q) + q, missing = 0;
    double per = 5.0 * n * Q5;
    long samples = argc > 3 ? atol(argv[3]) : (long)(2e9 / per);
    if (argc <= 3) samples = samples < 20 ? 20 : samples > 500 ? 500 : samples;
    uint32_t *stamp = calloc((size_t)Q5, sizeof(uint32_t));
    uint64_t sd = 0x2545F4914F6CDD1DULL;
    for (long t = 1; t <= samples; t++) {
        int col[5];
        for (;;) {
            for (int i = 0; i < 5; i++) { sd ^= sd << 13; sd ^= sd >> 7; sd ^= sd << 17; col[i] = (int)(sd % (uint64_t)k); }
            int dup = 0;
            for (int i = 0; i < 5; i++) for (int j = i + 1; j < 5; j++) dup |= col[i] == col[j];
            if (!dup) break;
        }
        long seen = 0;
        for (int r = 0; r < n; r++)
            for (long u = 0; u < Q4; u++) {
                int ud[4];
                long v = u;
                for (int i = 3; i >= 0; i--) { ud[i] = (int)(v % q); v /= q; }
                if (!u && r > 0) continue;  /* constant rows once */
                int bs[5];
                for (int i = 0; i < 5; i++) {
                    int acc = 0;
                    for (int c = 0; c < 4; c++) acc = ADD[acc][MUL[ud[c]][Xc[r][c][col[i]]]];
                    bs[i] = acc;
                }
                for (int u0 = 0; u0 < q; u0++) {
                    long code = 0;
                    for (int i = 0; i < 5; i++) code = code * q + ADD[u0][bs[i]];
                    if (stamp[code] != (uint32_t)t) { stamp[code] = (uint32_t)t; seen++; }
                }
            }
        if (seen != Q5) missing++;
    }
    printf("CA(%ld; 5, %d, %d): %ld random sets of five columns, %ld missing a tuple\n", N, k, q, samples, missing);
    if ((TFROM > 1 || TTO + 3 < k) && !strcmp(method, "fast")) {
        printf("PARTIAL: tasks x1 = %d..%d of 1..%d only (the verdict needs every task)\n", TFROM, TTO < k - 4 ? TTO : k - 4, k - 4);
        return bad ? 1 : 3;
    }
    printf("%s\n", bad || missing ? "FAIL" : "PASS");
    return bad || missing ? 1 : 0;
}
