/* Strength-5 Sherwood CPHFs in little memory: SCPHF(n; K, q^4, 5) whose first C rows are affine progressions of the
   two types of cphf5c.c (type 1: a^j in GF(q^4), a primitive; type 2: (s^j, j c) in GF(q^3) x GF(q), s primitive),
   the next rows random and the last rows built by local search. As in cphf5c.c, columns j1 < ... < j5 fail in every
   cyclic row exactly when 0, j2 - j1, ..., j5 - j1 do, so only the shifts of B, the sets holding column 0 that fail
   in all C cyclic rows, need the other rows. Where cphf5c.c's memory (4-16 GB) went, and what changed:
   - Copies of B. cphf5c.c kept a set of B in every bucket path holding it. A set whose points span only a line or a
     plane in a bucketed row lies on q + 1 (or q^2 + q + 1) of that row's planes through column 0's point, so it was
     kept that many times per level. Here a set is kept only in the bucket path of the smallest plane holding it at
     every level (the independent checker's count: the two agree exactly), so B is exact.
   - Buckets that never shrink. Columns whose points stay on one line through column 0's point row after row
     (multiples of q^2 + 1 in type-1 rows, the GF(q^2) plane; columns a period apart) share q + 1 planes in every
     row, so cphf5c.c split them again and again down to row C: (q + 1)^C bucket paths, each listing the same
     quadruples (q 9, 2,500 columns, type-1 rows: 10 GB in seconds). A bucket holding more than half of its parent's
     columns is now listed directly (at most LEAFMAX columns): that run takes 27 s and 5 MB.
   - Storage. cphf5c.c grew per-thread arrays by doubling and then copied them into one merged array (three copies
     at the peak). Here B is kept packed (four 16-bit offsets, 8 bytes a set) in fixed 8 MB blocks that are never
     copied, and only up to CPHF_BCAP sets; past that it is not stored but streamed: every set is tested against the
     random rows the moment the enumeration finds it (re-enumerated for each attempt; then about 10 MB in all).
   - Shifts. The shifted sets are never listed: each shift of each set of B is tested against R1 random rows as it
     is generated, and only the ones those rows leave (about F pbad^R1 of the F shifted sets) are kept, as five
     16-bit columns, capped at CPHF_UCAP.
   - Row types. cphf5c.c used type-1 rows alone when no type-2 row reaches order K (q 8 past 1,022 columns, q 9 past
     2,184). Every type-1 row puts columns congruent mod m = q^3 + q^2 + q + 1 on lines through the origin (a^m lies in
     GF(q)) and columns congruent mod q^2 + 1 on planes through it (GF(q^2)), so three columns on one such line, four
     on one such plane, or two pairs on two such lines (four points in a plane through the origin) fail in all
     type-1 rows: 1e11-1e12 shifted sets at 3,000-6,500 columns. Here type-2 rows may repeat within K columns: their
     coincident pairs (a period apart) and the sets of columns congruent mod p (one hyperplane w = const) fail in
     every type-2 row but are covered by the type-1 rows, while the type-2 rows cover the subfield sets. What fails
     both kinds (four on a GF(q^2) plane, all congruent mod p) cannot be avoided; q 9 with 6,560 columns, 6 + 3
     cyclic rows: B 40.8 million sets, 4.9e10 shifted sets (CPHF_CLASSIFY splits them by structure). Seeds differ
     (one in six drew a type-2 row that covers the subfield sets badly), so screen seeds at a smaller K (the rows
     depend on the seed only). Type-1 rows have order q^4 - 1, so columns that far apart coincide in all of them
     once K > q^4 - 1: allowed but costly (warned).
   - Last rows. Instead of redrawing the last row at random until it covers every leftover shifted set (hopeless past
     a few dozen), rows are drawn at random until at most CPHF_ULS sets are left, then built by local search: for a
     column, every point of AG(4,q) is scored at once by marking, for each leftover set holding the column, the
     hyperplane through its other four points (q^3 points each); min-conflicts moves (an uncovered set, the best
     point for whichever of its columns gains most) and, above 20 K sets, column sweeps first. One such row covers
     about 1e5 leftover sets at 6,560 columns (random sets: 100,000 in 0.7 s; 175,000 stall at about 300).
   Prints "best k K (q Q, n N, t 5, cyclic C, S s)" (N: rows used, at most n; best k 0 when it failed), a comment line
   with the fields and the cyclic rows, then the array (N lines of point ids ((x q + y) q + z) q + w).
   cc -O3 -o cphf5l cphf5l.c -lm -lpthread && ./cphf5l q n seconds seed K C1 C2 [R1]
     C1 type-1 rows and C2 <= C1 type-2 rows (row r is type 2 for odd r below 2 C2); R1 random rows tested in the stream
     (default: enough to leave about CPHF_UTARGET shifted sets).
   Environment: CPHF_THREADS (default 4), CPHF_BCAP (sets of B stored, default 1e8 = 800 MB), CPHF_UCAP (leftover
   shifted sets kept, default 2e7 = 200 MB), CPHF_UTARGET (default 1e6), CPHF_ULS (local search from this many
   leftover sets, default 15 K), CPHF_LSMAX (an attempt fails at once when more than this many sets are left for
   the last row, default 30 K), CPHF_LSROWS (rows kept for local search, default 1), CPHF_OUT=PREFIX (write each
   family found to PREFIX-n<rows>.txt and go on with one row fewer until the time is up), CPHF_COUNT=1 (only count
   B, its shifts and the copies cphf5c.c would keep; with CPHF_CLASSIFY=1 by structure, CPHF_DUMP=FILE listing some
   sets with none of the known structures), CPHF_LSTEST=m (local search alone against m random sets), CPHF_THR
   (bucket size listed directly), CPHF_LEAFMAX (largest non-shrinking bucket listed directly, default 160; 0 splits
   every bucket as cphf5c.c does). */
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <time.h>

#define MAXQ 25
#define MAXN 64
#define BLK (1L << 20) /* sets of B per storage block (8 MB) */

static int q, P, n, NN, NP;
static uint8_t ADD[32][32], SUB[32][32], MUL[32][32], INV[32];
static uint8_t *px, *py, *pz, *pw;
static uint8_t (*nv)[4];           /* the NN points of PG(3,q), first nonzero coordinate 1; also the planes' normals */
static int *dcls;                  /* direction class of each difference vector (as a point id), -1 for zero */
static int *ptpl;                  /* the NP = q^2 + q + 1 planes of PG(3,q) through each point, NP per point */
static uint64_t rng;

static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static uint64_t rndt(uint64_t *s) { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; return *s; }
static double now(void) { struct timeval t; gettimeofday(&t, NULL); return t.tv_sec + 1e-6 * t.tv_usec; }
static double T0;

static int field(int qq) {  /* GF(q) as in cphf5c.c (same polynomials as the independent checker) */
    static const struct { int q, p, m, poly[6]; } F[] = {
        {4, 2, 2, {1, 1, 1}}, {8, 2, 3, {1, 1, 0, 1}}, {16, 2, 4, {1, 1, 0, 0, 1}},
        {9, 3, 2, {1, 0, 1}}, {25, 5, 2, {2, 1, 1}}};
    int p = 0, m = 0; const int *poly = NULL;
    static int add[MAXQ][MAXQ], mul[MAXQ][MAXQ];
    for (int i = 0; i < 5; i++) if (F[i].q == qq) { p = F[i].p; m = F[i].m; poly = F[i].poly; }
    if (!p) {
        for (int d = 2; d * d <= qq; d++) if (qq % d == 0) return 0;
        for (int a = 0; a < qq; a++) for (int b = 0; b < qq; b++) { add[a][b] = (a + b) % qq; mul[a][b] = a * b % qq; }
    } else {
        for (int a = 0; a < qq; a++)
            for (int b = 0; b < qq; b++) {
                int da[8], db[8], s = 0, pwr = 1, prod[16] = {0};
                for (int i = 0, x = a, y = b; i < m; i++, x /= p, y /= p) { da[i] = x % p; db[i] = y % p; }
                for (int i = 0; i < m; i++) { s += ((da[i] + db[i]) % p) * pwr; pwr *= p; }
                add[a][b] = s;
                for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) prod[i + j] = (prod[i + j] + da[i] * db[j]) % p;
                for (int d = 2 * m - 2; d >= m; d--)
                    if (prod[d]) { int c = prod[d]; prod[d] = 0; for (int i = 0; i < m; i++) prod[d - m + i] = ((prod[d - m + i] - c * poly[i]) % p + p) % p; }
                s = 0; pwr = 1;
                for (int i = 0; i < m; i++) { s += prod[i] * pwr; pwr *= p; }
                mul[a][b] = s;
            }
    }
    for (int a = 0; a < qq; a++)
        for (int b = 0; b < qq; b++) {
            ADD[a][b] = (uint8_t)add[a][b]; MUL[a][b] = (uint8_t)mul[a][b];
            for (int c = 0; c < qq; c++) if (add[b][c] == a) SUB[a][b] = (uint8_t)c;
            if (mul[a][b] == 1) INV[a] = (uint8_t)b;
        }
    return 1;
}

static int dirclass(int a, int b, int c, int d) {  /* class of a nonzero vector: first nonzero coordinate 1 */
    if (a) { int s = INV[a]; return (MUL[b][s] * q + MUL[c][s]) * q + MUL[d][s]; }
    if (b) { int s = INV[b]; return q * q * q + MUL[c][s] * q + MUL[d][s]; }
    if (c) return q * q * q + q * q + MUL[d][INV[c]];
    return q * q * q + q * q + q;
}

static void geometry(void) {
    P = q * q * q * q; NN = q * q * q + q * q + q + 1; NP = q * q + q + 1;
    px = malloc(P); py = malloc(P); pz = malloc(P); pw = malloc(P);
    for (int p = 0; p < P; p++) { px[p] = (uint8_t)(p / (q * q * q)); py[p] = (uint8_t)(p / (q * q) % q); pz[p] = (uint8_t)(p / q % q); pw[p] = (uint8_t)(p % q); }
    nv = malloc(sizeof *nv * NN);
    for (int i = 0; i < NN; i++) {
        int a, b, c, d, j;
        if (i < q * q * q) { a = 1; b = i / (q * q); c = i / q % q; d = i % q; }
        else if ((j = i - q * q * q) < q * q) { a = 0; b = 1; c = j / q; d = j % q; }
        else if ((j -= q * q) < q) { a = 0; b = 0; c = 1; d = j; }
        else { a = 0; b = 0; c = 0; d = 1; }
        nv[i][0] = (uint8_t)a; nv[i][1] = (uint8_t)b; nv[i][2] = (uint8_t)c; nv[i][3] = (uint8_t)d;
        if (dirclass(a, b, c, d) != i) { fprintf(stderr, "PG(3,q) numbering is wrong\n"); exit(3); }
    }
    dcls = malloc(sizeof(int) * P);
    for (int v = 0; v < P; v++) dcls[v] = v ? dirclass(px[v], py[v], pz[v], pw[v]) : -1;
    ptpl = malloc(sizeof(int) * (size_t)NN * NP);
    for (int d = 0; d < NN; d++) {  /* plane l holds point d when nv[l] . nv[d] = 0 */
        int j = 0;
        for (int l = 0; l < NN; l++) {
            int s = ADD[ADD[MUL[nv[l][0]][nv[d][0]]][MUL[nv[l][1]][nv[d][1]]]][ADD[MUL[nv[l][2]][nv[d][2]]][MUL[nv[l][3]][nv[d][3]]]];
            if (!s) { if (j == NP) { fprintf(stderr, "PG(3,q) incidence is wrong\n"); exit(3); } ptpl[(size_t)d * NP + j++] = l; }
        }
        if (j != NP) { fprintf(stderr, "PG(3,q) incidence is wrong\n"); exit(3); }
    }
}

/* Normal of the span of u, v, s (generalised cross product): N . x = det[x; u; v; s]. */
#define SPAN_NORMAL(u0, u1, u2, u3, v0, v1, v2, v3, s0, s1, s2, s3, N0, N1, N2, N3) do { \
    int Q01 = SUB[MUL[s0][u1]][MUL[s1][u0]], Q02 = SUB[MUL[s0][u2]][MUL[s2][u0]], Q03 = SUB[MUL[s0][u3]][MUL[s3][u0]]; \
    int Q12 = SUB[MUL[s1][u2]][MUL[s2][u1]], Q13 = SUB[MUL[s1][u3]][MUL[s3][u1]], Q23 = SUB[MUL[s2][u3]][MUL[s3][u2]]; \
    N0 = ADD[SUB[MUL[v1][Q23]][MUL[v2][Q13]]][MUL[v3][Q12]]; \
    N1 = SUB[0][ADD[SUB[MUL[v0][Q23]][MUL[v2][Q03]]][MUL[v3][Q02]]]; \
    N2 = ADD[SUB[MUL[v0][Q13]][MUL[v1][Q03]]][MUL[v3][Q01]]; \
    N3 = SUB[0][ADD[SUB[MUL[v0][Q12]][MUL[v1][Q02]]][MUL[v2][Q01]]]; } while (0)

#define DOT4(N0, N1, N2, N3, x0, x1, x2, x3) ADD[ADD[MUL[N0][x0]][MUL[N1][x1]]][ADD[MUL[N2][x2]][MUL[N3][x3]]]

/* 1 when the five points (4 coordinates each) lie on one hyperplane */
static inline int dep5(const uint8_t *A, const uint8_t *B, const uint8_t *C_, const uint8_t *D, const uint8_t *E) {
    int u0 = SUB[B[0]][A[0]], u1 = SUB[B[1]][A[1]], u2 = SUB[B[2]][A[2]], u3 = SUB[B[3]][A[3]];
    int v0 = SUB[C_[0]][A[0]], v1 = SUB[C_[1]][A[1]], v2 = SUB[C_[2]][A[2]], v3 = SUB[C_[3]][A[3]];
    int s0 = SUB[D[0]][A[0]], s1 = SUB[D[1]][A[1]], s2 = SUB[D[2]][A[2]], s3 = SUB[D[3]][A[3]];
    int N0, N1, N2, N3;
    SPAN_NORMAL(u0, u1, u2, u3, v0, v1, v2, v3, s0, s1, s2, s3, N0, N1, N2, N3);
    return DOT4(N0, N1, N2, N3, SUB[E[0]][A[0]], SUB[E[1]][A[1]], SUB[E[2]][A[2]], SUB[E[3]][A[3]]) == 0;
}

static int nonzero_normal(const int *u, const int *v, const int *s) {
    int N0, N1, N2, N3;
    SPAN_NORMAL(u[0], u[1], u[2], u[3], v[0], v[1], v[2], v[3], s[0], s[1], s[2], s[3], N0, N1, N2, N3);
    return N0 | N1 | N2 | N3;
}

/* ---------------- rows ---------------- */
static int K, C, C1, C2;
static uint32_t *A[MAXN];          /* point ids, n rows of K */
static uint8_t *crd[MAXN];         /* the same as coordinates, 4 bytes a column */

static void setpt(int r, int j, uint32_t p) {
    A[r][j] = p;
    uint8_t *c = crd[r] + 4 * (size_t)j;
    c[0] = px[p]; c[1] = py[p]; c[2] = pz[p]; c[3] = pw[p];
}

static int f4c[4], f3c[3];         /* GF(q^4) = GF(q)[x]/(x^4 + f3 x^3 + ... + f0), GF(q^3) = GF(q)[x]/(x^3 + ... + g0) */
static uint32_t *ex, *ex3;         /* powers of a primitive element of each */
static long Qm1, Q3m1;
static int pchar;

static uint32_t enc(int c0, int c1, int c2, int c3) { return (uint32_t)(((c0 * q + c1) * q + c2) * q + c3); }

static uint32_t timesx(uint32_t a, int deg, const int *f) {
    int c[4] = {px[a], py[a], pz[a], pw[a]}, top = c[deg - 1], o[4] = {0, 0, 0, 0};
    o[0] = SUB[0][MUL[top][f[0]]];
    for (int i = 1; i < deg; i++) o[i] = SUB[c[i - 1]][MUL[top][f[i]]];
    return enc(o[0], o[1], o[2], o[3]);
}

static uint32_t fmul(uint32_t a, uint32_t b, int deg, const int *f) {
    int bc[4] = {px[b], py[b], pz[b], pw[b]};
    uint32_t r = 0;
    for (int i = deg - 1; i >= 0; i--) {
        r = timesx(r, deg, f);
        int t = bc[i];
        r = enc(ADD[px[r]][MUL[t][px[a]]], ADD[py[r]][MUL[t][py[a]]], ADD[pz[r]][MUL[t][pz[a]]], ADD[pw[r]][MUL[t][pw[a]]]);
    }
    return r;
}

static uint32_t fpow(uint32_t a, long e, int deg, const int *f) {
    uint32_t r = enc(1, 0, 0, 0);
    while (e) { if (e & 1) r = fmul(r, a, deg, f); a = fmul(a, a, deg, f); e >>= 1; }
    return r;
}

static int noroot(int deg, const int *f) {
    for (int a = 0; a < q; a++) {
        int v = 1;
        for (int i = deg - 1; i >= 0; i--) v = ADD[MUL[v][a]][f[i]];
        if (!v) return 0;
    }
    return 1;
}

static int irreducible4(void) {  /* no root and no monic quadratic factor */
    if (!noroot(4, f4c)) return 0;
    for (int b = 0; b < q; b++)
        for (int c = 0; c < q; c++) {
            int r[5] = {f4c[0], f4c[1], f4c[2], f4c[3], 1};
            for (int d = 4; d >= 2; d--) {
                int l = r[d];
                if (!l) continue;
                r[d] = 0; r[d - 1] = SUB[r[d - 1]][MUL[l][b]]; r[d - 2] = SUB[r[d - 2]][MUL[l][c]];
            }
            if (!r[0] && !r[1]) return 0;
        }
    return 1;
}

static uint32_t *powers(int deg, const int *f, long order) {
    long pr[16], m = order;
    int np = 0;
    for (long d = 2; d * d <= m; d++) if (m % d == 0) { pr[np++] = d; while (m % d == 0) m /= d; }
    if (m > 1) pr[np++] = m;
    uint32_t g, one = enc(1, 0, 0, 0);
    long size = 1;
    for (int i = 0; i < deg; i++) size *= q;
    for (;;) {
        long id = 1 + (long)(rnd() % (uint64_t)(size - 1));
        int c[4] = {0, 0, 0, 0};
        for (int i = deg - 1; i >= 0; i--) { c[i] = (int)(id % q); id /= q; }
        g = enc(c[0], c[1], c[2], c[3]);
        int ok = 1;
        for (int i = 0; i < np && ok; i++) ok = fpow(g, order / pr[i], deg, f) != one;
        if (ok) break;
    }
    uint32_t *e = malloc(sizeof(uint32_t) * order);
    e[0] = one;
    for (long i = 1; i < order; i++) e[i] = fmul(e[i - 1], g, deg, f);
    if (fmul(e[order - 1], g, deg, f) != one) { fprintf(stderr, "GF(q^%d) is wrong\n", deg); exit(3); }
    return e;
}

static long gcdl(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }

struct row { int type, c; long e; };

static long rclass(const struct row *R) {  /* rows a^e and a^(eq) differ by the Frobenius map, a linear one */
    long m = R->type == 1 ? Qm1 : Q3m1, b = R->e, x = R->e;
    for (int i = 1; i < (R->type == 1 ? 4 : 3); i++) { x = x * q % m; if (x < b) b = x; }
    return b * 2 + R->type - 1;
}

static inline uint32_t point(const struct row *R, long j) {
    if (R->type == 1) return ex[R->e * (j % Qm1) % Qm1];
    uint32_t u = ex3[R->e * (j % Q3m1) % Q3m1];  /* GF(q^3) element in the first three coordinates, j c in the last */
    return u + (uint32_t)MUL[j % pchar][R->c];
}

/* ---------------- B: sets {0, a, b, c, d} failing in every cyclic row ---------------- */
static int THR;
static long BCAP, UCAP;
static int MODE;                   /* 1: count (and store up to BCAP); 2: stream into the random rows */
static volatile long bstored; static volatile int bfull;
static int RR0, R1;                /* the random rows tested in the stream: RR0 .. RR0 + R1 - 1 */
static volatile long utotal; static volatile int uover;

struct ctx {
    int *ent[MAXN], *cnt[MAXN], *off[MAXN], *tch[MAXN], *cls[MAXN];
    long entcap[MAXN];
    int path[MAXN];
    uint8_t (*u)[4];
    long nb, ndup;                 /* canonical sets found; extra copies (what cphf5c.c kept besides) */
    double nshift, ntest;
    uint64_t **blocks; long *blockn; int nblocks, capblocks;
    uint16_t (*U)[5]; long nU, capU;
};

static void store(struct ctx *X, int a, int b, int c, int d) {
    if (bfull) return;
    if (!X->nblocks || X->blockn[X->nblocks - 1] == BLK) {
        if (__sync_add_and_fetch(&bstored, BLK) > BCAP) { bfull = 1; return; }
        if (X->nblocks == X->capblocks) {
            X->capblocks = X->capblocks ? 2 * X->capblocks : 16;
            X->blocks = realloc(X->blocks, sizeof(uint64_t *) * X->capblocks);
            X->blockn = realloc(X->blockn, sizeof(long) * X->capblocks);
        }
        X->blocks[X->nblocks] = malloc(sizeof(uint64_t) * BLK);
        X->blockn[X->nblocks++] = 0;
    }
    X->blocks[X->nblocks - 1][X->blockn[X->nblocks - 1]++] = (uint64_t)a << 48 | (uint64_t)b << 32 | (uint64_t)c << 16 | (uint64_t)d;
}

static void stream_set(struct ctx *X, int a, int b, int c, int d) {  /* every shift of {0, a, b, c, d}, against the
                                                                         R1 random rows; keep what they leave */
    for (int s = 0; s + d < K; s++) {
        int ok = 0, r;
        for (r = RR0; r < RR0 + R1; r++) {
            const uint8_t *R = crd[r];
            if (!dep5(R + 4 * s, R + 4 * (s + a), R + 4 * (s + b), R + 4 * (s + c), R + 4 * (s + d))) { ok = 1; r++; break; }
        }
        X->ntest += r - RR0;
        if (ok || uover) continue;
        if (X->nU == X->capU) {
            if (__sync_add_and_fetch(&utotal, X->capU ? X->capU : 4096) > UCAP) { uover = 1; continue; }
            X->capU = X->capU ? 2 * X->capU : 4096;
            X->U = realloc(X->U, sizeof *X->U * X->capU);
        }
        uint16_t *e = X->U[X->nU++];
        e[0] = (uint16_t)s; e[1] = (uint16_t)(s + a); e[2] = (uint16_t)(s + b); e[3] = (uint16_t)(s + c); e[4] = (uint16_t)(s + d);
    }
}

/* Is {0, a, b, c, d} counted in this bucket path? At every bucketed level its four difference vectors from column
   0's point lie on the bucket's plane; when they span 3 dimensions that plane is the only one, else the set is
   counted only where the plane is the smallest (by normal) holding all four: with two directions d1 != d2 among
   them (rank 2) the first plane through d1 (ptpl lists them in increasing order) whose normal is orthogonal to the
   d2 vector; with one direction (rank 1) the first plane through it; with none (all at column 0's point) plane 0. */
static int canonical(const struct ctx *X, int a, int b, int c, int d, int levels) {
    for (int l = 0; l < levels; l++) {
        const uint8_t *R = crd[l], *P0 = R, *pa = R + 4 * a, *pb = R + 4 * b, *pc = R + 4 * c, *pd = R + 4 * d;
        int u[4][4];
        for (int i = 0; i < 4; i++) { u[0][i] = SUB[pa[i]][P0[i]]; u[1][i] = SUB[pb[i]][P0[i]]; u[2][i] = SUB[pc[i]][P0[i]]; u[3][i] = SUB[pd[i]][P0[i]]; }
        if (nonzero_normal(u[0], u[1], u[2]) || nonzero_normal(u[0], u[1], u[3]) || nonzero_normal(u[0], u[2], u[3]) || nonzero_normal(u[1], u[2], u[3]))
            continue;
        int d1 = -1, d2 = -1, e2 = -1, minpl = 0;
        for (int j = 0; j < 4; j++) {
            int id = ((u[j][0] * q + u[j][1]) * q + u[j][2]) * q + u[j][3];
            if (!id) continue;
            int dc = dcls[id];
            if (d1 < 0) d1 = dc;
            else if (dc != d1 && d2 < 0) { d2 = dc; e2 = j; }
        }
        if (d1 >= 0 && d2 < 0) minpl = ptpl[(size_t)d1 * NP];
        else if (d1 >= 0) {
            minpl = -1;
            for (int j = 0; j < NP && minpl < 0; j++) {
                const uint8_t *N = nv[ptpl[(size_t)d1 * NP + j]];
                if (!DOT4(N[0], N[1], N[2], N[3], u[e2][0], u[e2][1], u[e2][2], u[e2][3])) minpl = ptpl[(size_t)d1 * NP + j];
            }
        }
        if (minpl != X->path[l]) return 0;
    }
    return 1;
}

/* CPHF_CLASSIFY=1: the shifted sets of B by structure (bit 0: all five columns congruent mod p, on one hyperplane
   w = const in every type-2 row; 1: two columns a type-2 period apart; 2: three congruent mod q^3+q^2+q+1, collinear
   in type-1 rows; 3: four congruent mod q^2+1, coplanar in type-1 rows; 4: three congruent mod q^3-1 and distinct
   mod the type-2 period, collinear in type-2 rows; 5: four congruent mod q^2+q+1, coplanar in type-2 rows; 6: two
   columns q^4-1 apart) */
static int classify;
static FILE *dumpf;                /* CPHF_DUMP=FILE: the first 200,000 sets of B with none of those structures */
static long cmod[7];
static double cls_f[128]; static long cls_n[128];
static pthread_mutex_t clsmx = PTHREAD_MUTEX_INITIALIZER;
static int structure(const int *s) {
    int f = 0;
    for (int bit = 0; bit < 7; bit++) {
        long m = cmod[bit];
        int need = bit == 0 ? 5 : bit == 1 || bit == 6 ? 2 : bit == 2 || bit == 4 ? 3 : 4;
        if (m <= 0) continue;
        for (int i = 0; i < 5 && !(f >> bit & 1); i++) {
            int cntm = 0, distinct[5], nd = 0;
            for (int j = 0; j < 5; j++)
                if ((s[j] - s[i]) % m == 0) {
                    cntm++;
                    if (bit == 4) {  /* distinct mod the type-2 period */
                        long r = s[j] % cmod[1]; int dup = 0;
                        for (int t = 0; t < nd; t++) dup |= distinct[t] == r;
                        if (!dup) distinct[nd++] = (int)r;
                    }
                }
            if (bit == 4 ? nd >= 3 : cntm >= need) f |= 1 << bit;
        }
    }
    return f;
}

static void found(struct ctx *X, int a, int b, int c, int d, int levels) {
    if (!canonical(X, a, b, c, d, levels)) { X->ndup++; return; }
    if (classify) {
        int s[5] = {0, a, b, c, d}, f = structure(s);
        pthread_mutex_lock(&clsmx); cls_f[f] += K - d; cls_n[f]++;
        if (dumpf && f == 0 && cls_n[0] <= 200000) fprintf(dumpf, "%d %d %d %d\n", a, b, c, d);
        pthread_mutex_unlock(&clsmx);
    }
    X->nb++; X->nshift += K - d;
    if (MODE == 2) stream_set(X, a, b, c, d); else store(X, a, b, c, d);
}

static void leaf(struct ctx *X, const int *L, int len, int r0) {  /* quadruples of L (with column 0 on one plane in
                                                                     rows 0..r0-1), filtered through rows r0..C-1 */
    if (len < 4) return;
    if (r0 >= C) {
        for (int x = 0; x < len; x++) for (int y = x + 1; y < len; y++) for (int z = y + 1; z < len; z++)
            for (int t = z + 1; t < len; t++) found(X, L[x], L[y], L[z], L[t], r0);
        return;
    }
    const uint8_t *R = crd[r0];
    uint8_t (*u)[4] = X->u;
    for (int j = 0; j < len; j++) { const uint8_t *pj = R + 4 * L[j]; for (int i = 0; i < 4; i++) u[j][i] = SUB[pj[i]][R[i]]; }
    for (int x = 0; x + 3 < len; x++) {
        int s0 = u[x][0], s1 = u[x][1], s2 = u[x][2], s3 = u[x][3];
        for (int y = x + 1; y + 2 < len; y++) {
            int u0 = u[y][0], u1 = u[y][1], u2 = u[y][2], u3 = u[y][3];
            int Q01 = SUB[MUL[s0][u1]][MUL[s1][u0]], Q02 = SUB[MUL[s0][u2]][MUL[s2][u0]], Q03 = SUB[MUL[s0][u3]][MUL[s3][u0]];
            int Q12 = SUB[MUL[s1][u2]][MUL[s2][u1]], Q13 = SUB[MUL[s1][u3]][MUL[s3][u1]], Q23 = SUB[MUL[s2][u3]][MUL[s3][u2]];
            for (int z = y + 1; z + 1 < len; z++) {
                int v0 = u[z][0], v1 = u[z][1], v2 = u[z][2], v3 = u[z][3];
                int N0 = ADD[SUB[MUL[v1][Q23]][MUL[v2][Q13]]][MUL[v3][Q12]];
                int N1 = SUB[0][ADD[SUB[MUL[v0][Q23]][MUL[v2][Q03]]][MUL[v3][Q02]]];
                int N2 = ADD[SUB[MUL[v0][Q13]][MUL[v1][Q03]]][MUL[v3][Q01]];
                int N3 = SUB[0][ADD[SUB[MUL[v0][Q12]][MUL[v1][Q02]]][MUL[v2][Q01]]];
                for (int t = z + 1; t < len; t++) {  /* N . u_t = det[u_t; u_y; u_z; u_x] */
                    if (DOT4(N0, N1, N2, N3, u[t][0], u[t][1], u[t][2], u[t][3])) continue;
                    int a = L[x], b = L[y], c = L[z], d = L[t], ok = 1;
                    for (int r = r0 + 1; r < C && ok; r++) {
                        const uint8_t *Rr = crd[r];
                        ok = dep5(Rr, Rr + 4 * a, Rr + 4 * b, Rr + 4 * c, Rr + 4 * d);
                    }
                    if (ok) found(X, a, b, c, d, r0);
                }
            }
        }
    }
}

static int split(struct ctx *X, int lev, const int *L, int len) {  /* buckets of L by the planes through column 0's
                                                                      point in row lev; returns how many planes */
    const uint8_t *R = crd[lev];
    int p0 = R[0], p1 = R[1], p2 = R[2], p3 = R[3];
    int *cnt = X->cnt[lev], *off = X->off[lev], *tch = X->tch[lev], *cl = X->cls[lev], nt = 0;
    long total = 0;
    for (int x = 0; x < len; x++) {
        const uint8_t *pa = R + 4 * L[x];
        int d = dcls[((SUB[pa[0]][p0] * q + SUB[pa[1]][p1]) * q + SUB[pa[2]][p2]) * q + SUB[pa[3]][p3]];
        cl[x] = d;
        if (d < 0) { for (int l = 0; l < NN; l++) if (cnt[l]++ == 0) tch[nt++] = l; total += NN; }
        else {
            const int *pl = ptpl + (size_t)d * NP;
            for (int j = 0; j < NP; j++) if (cnt[pl[j]]++ == 0) tch[nt++] = pl[j];
            total += NP;
        }
    }
    if (total > X->entcap[lev]) { X->entcap[lev] = total; X->ent[lev] = realloc(X->ent[lev], sizeof(int) * total); }
    int *e = X->ent[lev];
    long s = 0;
    for (int t = 0; t < nt; t++) { off[tch[t]] = (int)s; s += cnt[tch[t]]; }
    for (int x = 0; x < len; x++) {
        int d = cl[x];
        if (d < 0) for (int l = 0; l < NN; l++) e[off[l]++] = L[x];
        else { const int *pl = ptpl + (size_t)d * NP; for (int j = 0; j < NP; j++) e[off[pl[j]]++] = L[x]; }
    }
    return nt;
}

/* A bucket holding more than half of its parent's columns is not split again but listed (when it has at most
   LEAFMAX columns): such a bucket is a group of columns whose points stay on one line (or point) through column
   0's point row after row (multiples of q^2 + 1 in type-1 rows, of (q^3 - 1)/(q - 1) in type-2 rows, columns a
   period apart), which lies on q + 1 (or q^2 + q + 1) planes of each row, so splitting it again only copies it. */
static int LEAFMAX = 160;          /* CPHF_LEAFMAX; 0 splits every bucket, as cphf5c.c does */
static void bucket(struct ctx *X, int lev, const int *L, int len) {
    if (lev == C || len <= THR) { leaf(X, L, len, lev); return; }
    int nt = split(X, lev, L, len), *cnt = X->cnt[lev], *off = X->off[lev], *tch = X->tch[lev], *e = X->ent[lev];
    for (int t = 0; t < nt; t++) {
        int l = tch[t], c = cnt[l];
        if (c < 4) continue;
        X->path[lev] = l;
        if (c > THR && 2 * c > len && c <= LEAFMAX) leaf(X, e + off[l] - c, c, lev + 1);
        else bucket(X, lev + 1, e + off[l] - c, c);
    }
    for (int t = 0; t < nt; t++) cnt[tch[t]] = 0;
}

static struct ctx *CX;
static int nthreads, top_nt, top_next;
static int *Lall;

static void *worker(void *arg) {
    struct ctx *X = arg, *X0 = &CX[0];
    for (;;) {
        int t = __sync_fetch_and_add(&top_next, 1);
        if (t >= top_nt) return NULL;
        int l = X0->tch[0][t], c = X0->cnt[0][l];
        if (c >= 4) { X->path[0] = l; bucket(X, 1, X0->ent[0] + X0->off[0][l] - c, c); }
        if (MODE == 1 && (t + 1) % (top_nt / 10 + 1) == 0)
            fprintf(stderr, "  %d of %d row-0 planes, %.0f s\n", t + 1, top_nt, now() - T0);
    }
}

static void enumerate(void) {
    for (int w = 0; w < nthreads; w++) { CX[w].nb = CX[w].ndup = 0; CX[w].nshift = CX[w].ntest = 0; }
    int len = K - 1;
    if (C == 0 || len <= THR) { leaf(&CX[0], Lall, len, 0); return; }
    top_nt = split(&CX[0], 0, Lall, len);
    top_next = 0;
    pthread_t th[64];
    for (int w = 1; w < nthreads; w++) pthread_create(&th[w], NULL, worker, &CX[w]);
    worker(&CX[0]);
    for (int w = 1; w < nthreads; w++) pthread_join(th[w], NULL);
    for (int t = 0; t < top_nt; t++) CX[0].cnt[0][CX[0].tch[0][t]] = 0;
}

/* stream over the stored B: blocks shared out in pieces of 65,536 sets */
#define PIECE 65536L
static uint64_t **wblk; static long *wn, nwork; static volatile long wnext;
static long *wstart;               /* wstart[i]: first piece of block i */

static void *stream_worker(void *arg) {
    struct ctx *X = arg;
    for (;;) {
        long pc = __sync_fetch_and_add(&wnext, 1);
        if (pc >= nwork) return NULL;
        long b = 0;
        while (wstart[b + 1] <= pc) b++;
        long i0 = (pc - wstart[b]) * PIECE, i1 = i0 + PIECE < wn[b] ? i0 + PIECE : wn[b];
        const uint64_t *S = wblk[b];
        for (long i = i0; i < i1 && !uover; i++) {
            uint64_t t = S[i];
            stream_set(X, (int)(t >> 48), (int)(t >> 32 & 0xFFFF), (int)(t >> 16 & 0xFFFF), (int)(t & 0xFFFF));
        }
    }
}

/* ---------------- local search for one row ---------------- */
static uint64_t lsr;
static long ls_moves;
static int W4[4];                  /* point id = x0 W4[0] + x1 W4[1] + x2 W4[2] + x3 W4[3] */
static int *hc;                    /* per point: how many of the column's sets it would leave uncovered */

static void mark(int N0, int N1, int N2, int N3, int b, int add) {  /* hc += add on the hyperplane N . x = b */
    int N[4] = {N0, N1, N2, N3}, i0 = 0;
    while (!N[i0]) i0++;
    int iv = INV[N[i0]], f[3], k = 0;
    for (int i = 0; i < 4; i++) N[i] = MUL[N[i]][iv];
    b = MUL[b][iv];
    for (int i = 0; i < 4; i++) if (i != i0) f[k++] = i;
    for (int x1 = 0; x1 < q; x1++) {
        int s1 = MUL[N[f[0]]][x1], id1 = x1 * W4[f[0]];
        for (int x2 = 0; x2 < q; x2++) {
            int s2 = ADD[s1][MUL[N[f[1]]][x2]], id2 = id1 + x2 * W4[f[1]];
            for (int x3 = 0; x3 < q; x3++) hc[id2 + x3 * W4[f[2]] + SUB[b][ADD[s2][MUL[N[f[2]]][x3]]] * W4[i0]] += add;
        }
    }
}

/* The best point for column c of row R with the other columns fixed: each point x is scored by the sets holding c
   it would leave uncovered (x on the hyperplane through the other four points, or those four on no hyperplane at
   all); points leaving set must uncovered count 2^20 more, so they lose whenever some point covers it. Returns
   the count, *bv the point (ties: the first from a random start). */
static int best_point(uint16_t (*U)[5], const int *st, const int *adj, const uint8_t *R, int c, long must, uint32_t *bv) {
    memset(hc, 0, sizeof(int) * P);
    int dead = 0;
    for (int a = st[c]; a < st[c + 1]; a++) {
        long j = adj[a];
        const uint16_t *f = U[j];
        const uint8_t *B[4];
        int k = 0;
        for (int t = 0; t < 5; t++) if (f[t] != c) B[k++] = R + 4 * f[t];
        int N0, N1, N2, N3;
        SPAN_NORMAL(SUB[B[1][0]][B[0][0]], SUB[B[1][1]][B[0][1]], SUB[B[1][2]][B[0][2]], SUB[B[1][3]][B[0][3]],
                    SUB[B[2][0]][B[0][0]], SUB[B[2][1]][B[0][1]], SUB[B[2][2]][B[0][2]], SUB[B[2][3]][B[0][3]],
                    SUB[B[3][0]][B[0][0]], SUB[B[3][1]][B[0][1]], SUB[B[3][2]][B[0][2]], SUB[B[3][3]][B[0][3]], N0, N1, N2, N3);
        if (!(N0 | N1 | N2 | N3)) { dead++; continue; }
        mark(N0, N1, N2, N3, DOT4(N0, N1, N2, N3, B[0][0], B[0][1], B[0][2], B[0][3]), j == must ? 1 << 20 : 1);
    }
    int best = 1 << 30, x0 = (int)(rndt(&lsr) % P);
    for (int t = 0; t < P; t++) {
        int x = x0 + t < P ? x0 + t : x0 + t - P;
        if (hc[x] < best) { best = hc[x]; *bv = (uint32_t)x; }
    }
    return (best & ((1 << 20) - 1)) + (best >> 20) + dead;
}

/* Builds row r to cover as many sets of U as it can (all, when it can) by min-conflicts: an uncovered set, and for
   the one of its five columns that gains most, the best point of all q^4 (a random column one move in ten);
   stops when all are covered, after PATIENCE moves without a new best, or after secs. Returns how many it leaves. */
static long ls_row(uint16_t (*U)[5], long m, int r, double secs) {
    double t0 = now();
    int *deg = calloc(K + 1, sizeof(int)), *st = malloc(sizeof(int) * (K + 1));
    for (long i = 0; i < m; i++) for (int k = 0; k < 5; k++) deg[U[i][k]]++;
    st[0] = 0;
    for (int c = 0; c < K; c++) st[c + 1] = st[c] + deg[c];
    int *adj = malloc(sizeof(int) * (size_t)st[K] + 4), *fill = malloc(sizeof(int) * K);
    memcpy(fill, st, sizeof(int) * K);
    for (long i = 0; i < m; i++) for (int k = 0; k < 5; k++) adj[fill[U[i][k]]++] = (int)i;
    uint8_t *cov = malloc(m + 1);
    long *unc = malloc(sizeof(long) * (m + 1)), *pos = malloc(sizeof(long) * (m + 1)), nunc = 0;
    uint32_t *best = malloc(sizeof(uint32_t) * K);
    if (!hc) hc = malloc(sizeof(int) * P);
    uint8_t *R = crd[r];
    for (int c = 0; c < K; c++) setpt(r, c, (uint32_t)(rndt(&lsr) % P));
    for (long i = 0; i < m; i++) {
        cov[i] = !dep5(R + 4 * U[i][0], R + 4 * U[i][1], R + 4 * U[i][2], R + 4 * U[i][3], R + 4 * U[i][4]);
        if (cov[i]) pos[i] = -1; else { pos[i] = nunc; unc[nunc++] = i; }
    }
    /* Many sets per column: sweep the columns first (each to its best point given the others, until a sweep gains
       less than 0.5%), then the min-conflicts moves below. */
    if (m > 20L * K) {
        int *ord = malloc(sizeof(int) * K);
        for (int c = 0; c < K; c++) ord[c] = c;
        for (int sweep = 1; sweep <= 20 && now() - t0 < secs / 2; sweep++) {
            long before = nunc;
            for (int c = K - 1; c > 0; c--) { int j = (int)(rndt(&lsr) % (uint64_t)(c + 1)), t = ord[c]; ord[c] = ord[j]; ord[j] = t; }
            for (int oi = 0; oi < K; oi++) {
                int c = ord[oi], cur = 0;
                if (st[c + 1] == st[c]) continue;
                for (int a = st[c]; a < st[c + 1]; a++) cur += !cov[adj[a]];
                uint32_t v;
                if (best_point(U, st, adj, R, c, -1, &v) >= cur) continue;
                setpt(r, c, v);
                for (int a = st[c]; a < st[c + 1]; a++) {
                    long j = adj[a];
                    const uint16_t *f = U[j];
                    int nc = !dep5(R + 4 * f[0], R + 4 * f[1], R + 4 * f[2], R + 4 * f[3], R + 4 * f[4]);
                    if (nc == cov[j]) continue;
                    cov[j] = (uint8_t)nc;
                    if (nc) { long p = pos[j]; unc[p] = unc[--nunc]; pos[unc[p]] = p; pos[j] = -1; }
                    else { pos[j] = nunc; unc[nunc++] = j; }
                }
            }
            fprintf(stderr, "    row %d: sweep %d: %ld of %ld left, %.0f s\n", r, sweep, nunc, m, now() - t0);
            if (before - nunc < before / 200) break;
        }
        free(ord);
    }
    long bestunc = nunc, moves = 0, since = 0, patience = 20000 + 20 * nunc;
    memcpy(best, A[r], sizeof(uint32_t) * K);
    while (nunc && since < patience && now() - t0 < secs) {
        long i = unc[rndt(&lsr) % nunc];
        int bk = -1, bgain = -(1 << 30), nties = 0, gain[5];
        uint32_t v[5];
        for (int k = 0; k < 5; k++) {
            int c = U[i][k], cur = 0;
            for (int a = st[c]; a < st[c + 1]; a++) cur += !cov[adj[a]];
            gain[k] = cur - best_point(U, st, adj, R, c, i, &v[k]);
            if (gain[k] > bgain) { bgain = gain[k]; bk = k; nties = 1; }
            else if (gain[k] == bgain && rndt(&lsr) % (uint64_t)(++nties) == 0) bk = k;
        }
        if (rndt(&lsr) % 10 == 0) bk = (int)(rndt(&lsr) % 5);
        int c = U[i][bk];
        setpt(r, c, v[bk]);
        moves++;
        for (int a = st[c]; a < st[c + 1]; a++) {
            long j = adj[a];
            const uint16_t *f = U[j];
            int nc = !dep5(R + 4 * f[0], R + 4 * f[1], R + 4 * f[2], R + 4 * f[3], R + 4 * f[4]);
            if (nc == cov[j]) continue;
            cov[j] = (uint8_t)nc;
            if (nc) { long p = pos[j]; unc[p] = unc[--nunc]; pos[unc[p]] = p; pos[j] = -1; }
            else { pos[j] = nunc; unc[nunc++] = j; }
        }
        if (nunc < bestunc) { bestunc = nunc; memcpy(best, A[r], sizeof(uint32_t) * K); since = 0; }
        else since++;
        if (moves % 20000 == 0) fprintf(stderr, "    row %d: %ld moves, %ld left (best %ld), %.0f s\n", r, moves, nunc, bestunc, now() - t0);
    }
    for (int c = 0; c < K; c++) setpt(r, c, best[c]);
    ls_moves += moves;
    free(deg); free(st); free(adj); free(fill); free(cov); free(unc); free(pos); free(best);
    return bestunc;
}

static long filter(uint16_t (*U)[5], long m, int r) {  /* keep the sets row r leaves */
    const uint8_t *R = crd[r];
    long k2 = 0;
    for (long i = 0; i < m; i++)
        if (dep5(R + 4 * U[i][0], R + 4 * U[i][1], R + 4 * U[i][2], R + 4 * U[i][3], R + 4 * U[i][4])) memmove(U[k2++], U[i], sizeof *U);
    return k2;
}

static long peak_rss_mb(void) { struct rusage ru; getrusage(RUSAGE_SELF, &ru); return ru.ru_maxrss / (1024 * 1024); }

static long used[MAXN]; static int nused;

static struct row pick(int type) {  /* a random row of the type, its multiplier primitive, class not used yet */
    struct row R;
    R.type = type;
    for (;;) {
        long m = type == 1 ? Qm1 : Q3m1;
        R.e = 1 + (long)(rnd() % (uint64_t)(m - 1));
        R.c = 1 + (int)(rnd() % (q - 1));
        if (gcdl(R.e, m) != 1) continue;
        long c = rclass(&R);
        int dup = 0;
        for (int i = 0; i < nused; i++) dup |= used[i] == c;
        if (!dup) return R;
    }
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: cphf5l q n seconds seed K C1 C2 [R1]\n"); return 2; }
    q = atoi(argv[1]); n = atoi(argv[2]);
    double secs = atof(argv[3]);
    uint64_t seed = (uint64_t)atoll(argv[4]);
    rng = 0x9E3779B97F4A7C15ULL ^ seed * 0xD1B54A32D192ED03ULL;
    lsr = rng ^ 0x5851F42D4C957F2DULL;
    K = atoi(argv[5]); C1 = atoi(argv[6]); C2 = atoi(argv[7]); C = C1 + C2;
    int R1arg = argc > 8 ? atoi(argv[8]) : 0;
    if (q > MAXQ || n > MAXN || n < 2 || !field(q)) { fprintf(stderr, "q must be a supported prime power <= %d, n <= %d\n", MAXQ, MAXN); return 2; }
    if (K < 6 || K > 65535) { fprintf(stderr, "need 6 <= K <= 65535\n"); return 2; }
    if (C1 < 1 || C2 < 0 || C2 > C1 || C > n - 2) { fprintf(stderr, "need 1 <= C1, 0 <= C2 <= C1, C1 + C2 <= n - 2\n"); return 2; }
    T0 = now();
    geometry();
    do { for (int i = 0; i < 4; i++) f4c[i] = (int)(rnd() % q); } while (!irreducible4());
    do { for (int i = 0; i < 3; i++) f3c[i] = (int)(rnd() % q); } while (!noroot(3, f3c));
    Qm1 = (long)P - 1; Q3m1 = (long)q * q * q - 1;
    ex = powers(4, f4c, Qm1);
    ex3 = powers(3, f3c, Q3m1);
    pchar = 2;
    while (q % pchar) pchar++;
    cmod[0] = pchar; cmod[1] = Q3m1 * pchar; cmod[2] = Qm1 / (q - 1); cmod[3] = (long)q * q + 1; cmod[4] = Q3m1;
    cmod[5] = Q3m1 / (q - 1); cmod[6] = Qm1;
    nthreads = getenv("CPHF_THREADS") ? atoi(getenv("CPHF_THREADS")) : 4;
    if (nthreads < 1) nthreads = 1;
    if (nthreads > 64) nthreads = 64;
    BCAP = getenv("CPHF_BCAP") ? atol(getenv("CPHF_BCAP")) : 100000000L;
    UCAP = getenv("CPHF_UCAP") ? atol(getenv("CPHF_UCAP")) : 20000000L;
    double utarget = getenv("CPHF_UTARGET") ? atof(getenv("CPHF_UTARGET")) : 1e6;
    long ULS = getenv("CPHF_ULS") ? atol(getenv("CPHF_ULS")) : 15L * K;
    long LSMAX = getenv("CPHF_LSMAX") ? atol(getenv("CPHF_LSMAX")) : 30L * K;
    int LSROWS = getenv("CPHF_LSROWS") ? atoi(getenv("CPHF_LSROWS")) : 1;  /* rows kept for local search */
    if (LSROWS < 1) LSROWS = 1;
    int countonly = getenv("CPHF_COUNT") && atoi(getenv("CPHF_COUNT"));
    classify = getenv("CPHF_CLASSIFY") && atoi(getenv("CPHF_CLASSIFY"));
    if (classify && getenv("CPHF_DUMP")) dumpf = fopen(getenv("CPHF_DUMP"), "w");
    const char *outp = getenv("CPHF_OUT");  /* each family found goes to CPHF_OUT-n<rows>.txt, then one row fewer */
    int best_rows = 0;
    THR = getenv("CPHF_THR") ? atoi(getenv("CPHF_THR")) : (int)(1.3 * cbrt(24.0 * NP));
    W4[0] = q * q * q; W4[1] = q * q; W4[2] = q; W4[3] = 1;
    if (getenv("CPHF_LEAFMAX")) LEAFMAX = atoi(getenv("CPHF_LEAFMAX"));
    for (int r = 0; r < n; r++) { A[r] = malloc(sizeof(uint32_t) * K); crd[r] = malloc(4 * (size_t)K); }
    CX = calloc(nthreads, sizeof(struct ctx));
    for (int w = 0; w < nthreads; w++) {
        struct ctx *X = &CX[w];
        for (int r = 0; r < C; r++) {
            X->cls[r] = malloc(sizeof(int) * K);
            X->cnt[r] = calloc(NN, sizeof(int)); X->off[r] = malloc(sizeof(int) * NN); X->tch[r] = malloc(sizeof(int) * NN);
        }
        X->u = malloc(4 * (size_t)K);
    }
    Lall = malloc(sizeof(int) * K);
    for (int i = 0; i < K - 1; i++) Lall[i] = i + 1;
    if (getenv("CPHF_LSTEST")) {  /* capacity test: one local-search row against m random sets of five columns */
        long m = atol(getenv("CPHF_LSTEST"));
        uint16_t (*U)[5] = malloc(sizeof *U * m);
        for (long i = 0; i < m; i++) {
            for (;;) {
                for (int k = 0; k < 5; k++) U[i][k] = (uint16_t)(rnd() % K);
                int dup = 0;
                for (int a = 0; a < 5; a++) for (int b = a + 1; b < 5; b++) dup |= U[i][a] == U[i][b];
                if (!dup) break;
            }
        }
        for (int r = 0; r < n && m; r++) {
            double t = now();
            long left = ls_row(U, m, r, secs);
            fprintf(stderr, "LS test: row %d, %ld sets (%.1f per column): %ld left, %ld moves, %.1f s\n", r, m, 5.0 * m / K, left, ls_moves, now() - t);
            m = filter(U, m, r);
        }
        return 0;
    }
    /* cyclic rows */
    struct row rows[MAXN];
    for (int r = 0; r < C; r++) {
        rows[r] = pick(r % 2 == 1 && r / 2 < C2 ? 2 : 1);
        used[nused++] = rclass(&rows[r]);
        for (int j = 0; j < K; j++) setpt(r, j, point(&rows[r], j));
    }
    double pbad = 1 - (1 - pow(q, -4)) * (1 - pow(q, -3)) * (1 - pow(q, -2)) * (1 - pow(q, -1));
    long per2 = Q3m1 * pchar;
    fprintf(stderr, "q %d, K %d, n <= %d: %d cyclic rows (%d type 1, period %ld; %d type 2, period %ld), %d threads, THR %d\n",
            q, K, n, C, C1, Qm1, C2, per2, nthreads, THR);
    if (K > Qm1) fprintf(stderr, "warning: K > q^4 - 1: columns %ld apart coincide in every type-1 row\n", Qm1);
    if (C2 && K > per2) fprintf(stderr, "type-2 rows repeat: columns %ld apart coincide in them (covered by the type-1 rows)\n", per2);
    /* B, counted once (and kept when it fits) */
    MODE = 1;
    enumerate();
    long nb = 0, ndup = 0; double F = 0;
    for (int w = 0; w < nthreads; w++) { nb += CX[w].nb; ndup += CX[w].ndup; F += CX[w].nshift; }
    int stored = !bfull;
    fprintf(stderr, "B: %ld sets holding column 0 fail in all %d cyclic rows (cphf5c.c would keep %ld copies, %.1f GB at 8 bytes "
            "each, before its doubling and merged copy); %.4g shifted sets; %s; %.0f s, peak RSS %ld MB\n",
            nb, C, nb + ndup, (nb + ndup) * 8e-9, F, stored ? "stored" : "too many to store: streamed", now() - T0, peak_rss_mb());
    if (classify) {
        fprintf(stderr, "structure of the shifted sets (bits: 0 all = mod p, 1 type-2 coincident pair, 2 type-1 line triple, "
                "3 type-1 plane quadruple, 4 type-2 vertical triple, 5 type-2 plane quadruple, 6 type-1 coincident pair):\n");
        for (int f = 0; f < 128; f++) if (cls_n[f]) fprintf(stderr, "  %3d: %ld sets, %.4g shifted (%.1f%%)\n", f, cls_n[f], cls_f[f], 100 * cls_f[f] / F);
    }
    if (dumpf) fclose(dumpf);
    if (countonly) return 0;
    if (!stored) {  /* free the partial store */
        for (int w = 0; w < nthreads; w++) { for (int b = 0; b < CX[w].nblocks; b++) free(CX[w].blocks[b]); CX[w].nblocks = 0; }
        bstored = 0;
    } else {
        int nbk = 0;
        for (int w = 0; w < nthreads; w++) nbk += CX[w].nblocks;
        wblk = malloc(sizeof(uint64_t *) * (nbk + 1)); wn = malloc(sizeof(long) * (nbk + 1)); wstart = malloc(sizeof(long) * (nbk + 2));
        int b = 0;
        for (int w = 0; w < nthreads; w++) for (int i = 0; i < CX[w].nblocks; i++) { wblk[b] = CX[w].blocks[i]; wn[b++] = CX[w].blockn[i]; }
        wstart[0] = 0;
        for (int i = 0; i < nbk; i++) wstart[i + 1] = wstart[i] + (wn[i] + PIECE - 1) / PIECE;
        nwork = wstart[nbk];
    }
    R1 = R1arg > 0 ? R1arg : 1;
    if (R1arg <= 0) while (F * pow(pbad, R1) > utarget && R1 < n - C - LSROWS) R1++;
    if (R1 > n - C - LSROWS) R1 = n - C - LSROWS;
    for (int att = 1; now() - T0 < secs; att++) {
        RR0 = C;
        for (int r = C; r < C + R1; r++) for (int j = 0; j < K; j++) setpt(r, j, (uint32_t)(rnd() % P));
        utotal = 0; uover = 0;
        for (int w = 0; w < nthreads; w++) { CX[w].nU = 0; CX[w].ntest = 0; }
        double ts = now();
        if (stored) {
            wnext = 0;
            pthread_t th[64];
            for (int w = 1; w < nthreads; w++) pthread_create(&th[w], NULL, stream_worker, &CX[w]);
            stream_worker(&CX[0]);
            for (int w = 1; w < nthreads; w++) pthread_join(th[w], NULL);
        } else { MODE = 2; enumerate(); }
        long m = 0; double tests = 0;
        for (int w = 0; w < nthreads; w++) { m += CX[w].nU; tests += CX[w].ntest; }
        fprintf(stderr, "attempt %d: %d random rows leave %ld of the %.4g shifted sets (%.3g row tests, %.0f s; total %.0f s, peak RSS %ld MB)\n",
                att, R1, m, F, tests, now() - ts, now() - T0, peak_rss_mb());
        if (uover) {
            fprintf(stderr, "  more than CPHF_UCAP = %ld left: one more random row in the stream\n", UCAP);
            for (int w = 0; w < nthreads; w++) { free(CX[w].U); CX[w].U = NULL; CX[w].capU = CX[w].nU = 0; }
            if (R1 < n - C - 1) R1++;
            continue;
        }
        uint16_t (*U)[5] = malloc(sizeof *U * (m + 1));
        long o = 0;
        for (int w = 0; w < nthreads; w++) {
            memcpy(U + o, CX[w].U, sizeof *U * CX[w].nU); o += CX[w].nU;
            free(CX[w].U); CX[w].U = NULL; CX[w].capU = CX[w].nU = 0;
        }
        int used_rows = C + R1, first_ls = -1;
        while (m > ULS && used_rows < n - LSROWS) {
            for (int j = 0; j < K; j++) setpt(used_rows, j, (uint32_t)(rnd() % P));
            m = filter(U, m, used_rows);
            fprintf(stderr, "  random row %d: %ld left\n", used_rows, m);
            used_rows++;
        }
        if (n - used_rows == 1 && m > LSMAX) {  /* more than one local-search row can take: fail fast */
            fprintf(stderr, "  %ld sets left for the last row: more than CPHF_LSMAX = %ld\n", m, LSMAX);
            free(U);
            continue;
        }
        while (m > 0 && used_rows < n) {
            if (first_ls < 0) first_ls = used_rows;
            if (used_rows == n - 1 && m > LSMAX) { fprintf(stderr, "  %ld sets left for the last row: more than CPHF_LSMAX\n", m); break; }
            long left = ls_row(U, m, used_rows, used_rows == n - 1 ? 600 : 900);
            m = filter(U, m, used_rows);
            if (m != left) { fprintf(stderr, "local search count is wrong (%ld vs %ld)\n", m, left); return 3; }
            fprintf(stderr, "  local-search row %d: %ld left (%ld moves so far, %.0f s)\n", used_rows, m, ls_moves, now() - T0);
            used_rows++;
        }
        free(U);
        if (m) { fprintf(stderr, "  %ld sets left with all %d rows used\n", m, n); continue; }
        /* spot check: random sets of five columns, each covered in some row */
        long bad = 0;
        for (long t = 0; t < 200000; t++) {
            int c[5];
            for (;;) {
                for (int i = 0; i < 5; i++) c[i] = (int)(rnd() % K);
                int dup = 0;
                for (int i = 0; i < 5; i++) for (int j = i + 1; j < 5; j++) dup |= c[i] == c[j];
                if (!dup) break;
            }
            int ok = 0;
            for (int r = 0; r < used_rows && !ok; r++) {
                const uint8_t *R = crd[r];
                ok = !dep5(R + 4 * c[0], R + 4 * c[1], R + 4 * c[2], R + 4 * c[3], R + 4 * c[4]);
            }
            bad += !ok;
        }
        if (bad) { fprintf(stderr, "spot check: %ld of 200,000 random sets uncovered: a bug\n", bad); return 3; }
        if (first_ls < 0) first_ls = used_rows;
        FILE *fo = stdout;
        char path[4096];
        if (outp) { snprintf(path, sizeof path, "%s-n%d.txt", outp, used_rows); fo = fopen(path, "w"); if (!fo) { perror(path); return 2; } }
        fprintf(fo, "best k %d (q %d, n %d, t 5, cyclic %d, %.0f s)\n", K, q, used_rows, C, now() - T0);
        fprintf(fo, "# cphf5l seed %llu; GF(%d^4) mod x^4 + %d x^3 + %d x^2 + %d x + %d, GF(%d^3) mod x^3 + %d x^2 + %d x + %d; cyclic rows (type, step):",
                (unsigned long long)seed, q, f4c[3], f4c[2], f4c[1], f4c[0], q, f3c[2], f3c[1], f3c[0]);
        for (int r = 0; r < C; r++) fprintf(fo, " (%d, %u%s%d)", rows[r].type, rows[r].type == 1 ? ex[rows[r].e] : ex3[rows[r].e],
                                            rows[r].type == 1 ? "" : " + ", rows[r].type == 1 ? 0 : rows[r].c);
        fprintf(fo, "; B %ld sets, %.0f shifted; rows %d..%d random (%d..%d tested in the stream), %d..%d local search\n", nb, F, C,
                first_ls - 1, C, C + R1 - 1, first_ls, used_rows - 1);
        for (int r = 0; r < used_rows; r++) {
            for (int j = 0; j < K; j++) fprintf(fo, j ? " %u" : "%u", A[r][j]);
            fprintf(fo, "\n");
        }
        if (fo != stdout) fclose(fo);
        fprintf(stderr, "done: %d rows%s%s, %.0f s, peak RSS %ld MB\n", used_rows, outp ? " -> " : "", outp ? path : "", now() - T0, peak_rss_mb());
        if (!outp) return 0;
        best_rows = used_rows;
        n = used_rows - 1;  /* CPHF_OUT: keep going with one row fewer until the time is up */
        if (R1 > n - C - LSROWS) R1 = n - C - LSROWS;
        if (R1 < 1) break;
    }
    if (best_rows) return 0;
    printf("best k 0 (q %d, n %d, t 5, cyclic %d, %.0f s)\n", q, n, C, now() - T0);
    return 1;
}
