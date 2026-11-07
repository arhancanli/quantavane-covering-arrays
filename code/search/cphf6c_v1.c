/* Strength-6 Sherwood CPHFs with thousands of columns, part cyclic: SCPHF(n; K, q^5, 6), an n x K array of points
   of AG(5,q) in which any six columns hold, in some row, six points not on one hyperplane; by Sherwood, Martirosyan
   and Colbourn (2006) it gives CA(n(q^6 - q) + q; 6, K, q). As cphf5c.c, one dimension up: rows 0..C-1 are powers
   a^j of elements a of GF(q^5) = GF(q)[x]/(f) (basis 1, x, ..., x^4; order of a at least K, Frobenius classes
   distinct). Multiplying such a row by a^s is a linear map onto the row shifted by s, which keeps points on or off
   a hyperplane, so columns j1 < ... < j6 fail in all cyclic rows exactly when 0, j2 - j1, ..., j6 - j1 do.
   GF(q^5) has no subfield but GF(q), which the powers reach only at multiples of (q^5 - 1)/(q - 1) (2,801 for
   q = 7, more for larger q), so below that the cyclic rows have no built-in failing sets. The sets holding column 0
   that fail in every cyclic row are found by bucketing the other columns by every hyperplane of PG(4,q) through
   their direction from column 0's point, row by row: the five-sets sharing a bucket are exactly those on one
   hyperplane with column 0 in the rows bucketed so far. A bucket of at most THR columns is listed directly (one dot
   product per five-set, against a normal built once per quadruple from exterior products) and filtered through the
   remaining cyclic rows. Rows C..n-2 are random points checked against every shift of every such set; the last row
   is redrawn until it covers every shifted set the others leave, and the random rows are redrawn until that works.
   The bucketing runs on CPHF_THREADS threads (default 6), sharing out the row-0 hyperplanes.
   Prints "best k K (q Q, n N, t 6, cyclic C, S s)" (best k 0 when it failed), a comment line with the field and the
   cyclic rows, then the array (n lines of point ids (((x0 q + x1) q + x2) q + x3) q + x4).
   cc -O3 -o cphf6c cphf6c.c -lm -lpthread && ./cphf6c q n seconds seed K [C] (CPHF_THR sets THR) */
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 25
#define MAXN 40
#define MAXK 4096                  /* columns: a kept set is five 12-bit column numbers */
#define WILD 0xFFFFFFFFu           /* a column standing on column 0's point lies on every hyperplane through it */

static int q, P, n, NN, NPH, OFS[5];
static int add[MAXQ][MAXQ], mul[MAXQ][MAXQ], sub[MAXQ][MAXQ], inv[MAXQ];
static uint8_t *cx[5];             /* coordinates of each point id */
static uint64_t rng;

static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static int field(int qq) {  /* GF(q) as in cphf4m.c */
    static const struct { int q, p, m, poly[6]; } F[] = {
        {4, 2, 2, {1, 1, 1}}, {8, 2, 3, {1, 1, 0, 1}}, {16, 2, 4, {1, 1, 0, 0, 1}},
        {9, 3, 2, {1, 0, 1}}, {25, 5, 2, {2, 1, 1}}};
    int p = 0, m = 0; const int *poly = NULL;
    for (int i = 0; i < 5; i++) if (F[i].q == qq) { p = F[i].p; m = F[i].m; poly = F[i].poly; }
    if (!p) {
        for (int d = 2; d * d <= qq; d++) if (qq % d == 0) return 0;
        for (int a = 0; a < qq; a++) for (int b = 0; b < qq; b++) { add[a][b] = (a + b) % qq; mul[a][b] = a * b % qq; }
    } else {
        for (int a = 0; a < qq; a++)
            for (int b = 0; b < qq; b++) {
                int da[8], db[8], s = 0, pw = 1, prod[16] = {0};
                for (int i = 0, x = a, y = b; i < m; i++, x /= p, y /= p) { da[i] = x % p; db[i] = y % p; }
                for (int i = 0; i < m; i++) { s += ((da[i] + db[i]) % p) * pw; pw *= p; }
                add[a][b] = s;
                for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) prod[i + j] = (prod[i + j] + da[i] * db[j]) % p;
                for (int d = 2 * m - 2; d >= m; d--)
                    if (prod[d]) { int c = prod[d]; prod[d] = 0; for (int i = 0; i < m; i++) prod[d - m + i] = ((prod[d - m + i] - c * poly[i]) % p + p) % p; }
                s = 0; pw = 1;
                for (int i = 0; i < m; i++) { s += prod[i] * pw; pw *= p; }
                mul[a][b] = s;
            }
    }
    for (int a = 0; a < qq; a++)
        for (int b = 0; b < qq; b++) {
            for (int c = 0; c < qq; c++) if (add[b][c] == a) sub[a][b] = c;
            if (mul[a][b] == 1) inv[a] = b;
        }
    return 1;
}

static int dirclass(const int *v) {  /* class of a nonzero vector of GF(q)^5 (first nonzero coordinate made 1) */
    int i = 0;
    while (!v[i]) i++;
    int s = inv[v[i]], idx = 0;
    for (int j = i + 1; j < 5; j++) idx = idx * q + mul[v[j]][s];
    return OFS[i] + idx;
}

static void geometry(void) {
    P = q * q * q * q * q; NN = (P - 1) / (q - 1); NPH = (q * q * q * q - 1) / (q - 1);
    OFS[0] = 0;
    for (int i = 1; i < 5; i++) { int w = 1; for (int j = i; j < 5; j++) w *= q; OFS[i] = OFS[i - 1] + w; }
    for (int c = 0; c < 5; c++) cx[c] = malloc(P);
    for (int p = 0; p < P; p++) { int v = p; for (int c = 4; c >= 0; c--) { cx[c][p] = (uint8_t)(v % q); v /= q; } }
}

static inline void dir(uint32_t X, uint32_t p, int *v) { for (int c = 0; c < 5; c++) v[c] = sub[cx[c][X]][cx[c][p]]; }

static int hyps(const int *d, uint32_t *out) {  /* every hyperplane of PG(4,q) through direction d (normal classes) */
    int i0 = 0;
    while (!d[i0]) i0++;
    int s = inv[d[i0]], fi[4], nf = 0, cnt = 0;
    for (int j = 0; j < 5; j++) if (j != i0) fi[nf++] = j;
    for (int l = 0; l < 4; l++) {  /* free coordinates g (on fi), first nonzero g_l = 1; h_i0 makes h . d = 0 */
        int span = 1;
        for (int j = l + 1; j < 4; j++) span *= q;
        for (int t = 0; t < span; t++) {
            int g[4] = {0, 0, 0, 0}, h[5], v = t;
            g[l] = 1;
            for (int j = 3; j > l; j--) { g[j] = v % q; v /= q; }
            int acc = 0;
            for (int j = 0; j < 4; j++) { h[fi[j]] = g[j]; acc = add[acc][mul[g[j]][d[fi[j]]]]; }
            h[i0] = sub[0][mul[acc][s]];
            out[cnt++] = (uint32_t)dirclass(h);
        }
    }
    return cnt;
}

/* Exterior products in GF(q)^5: pairs 01 02 03 04 12 13 14 23 24 34, triples 012 013 014 023 024 034 123 124 134 234.
   N(a, b, c, d)_m = (-1)^m (a^b^c^d) without m, so N . e = det(a, b, c, d, e). */
static inline void wedge2(const int *a, const int *b, int *B) {
    static const int I[10] = {0, 0, 0, 0, 1, 1, 1, 2, 2, 3}, J[10] = {1, 2, 3, 4, 2, 3, 4, 3, 4, 4};
    for (int t = 0; t < 10; t++) B[t] = sub[mul[a[I[t]]][b[J[t]]]][mul[a[J[t]]][b[I[t]]]];
}
static inline int pidx(int i, int j) { static const int base[4] = {0, 4, 7, 9}; return base[i] + j - i - 1; }
static inline void wedge3(const int *B, const int *c, int *T) {  /* T_ijk = B_ij c_k - B_ik c_j + B_jk c_i */
    static const int I[10] = {0, 0, 0, 0, 0, 0, 1, 1, 1, 2}, J[10] = {1, 1, 1, 2, 2, 3, 2, 2, 3, 3}, K[10] = {2, 3, 4, 3, 4, 4, 3, 4, 4, 4};
    for (int t = 0; t < 10; t++) {
        int i = I[t], j = J[t], k = K[t];
        T[t] = add[sub[mul[B[pidx(i, j)]][c[k]]][mul[B[pidx(i, k)]][c[j]]]][mul[B[pidx(j, k)]][c[i]]];
    }
}
static inline int tidx(int i, int j, int k) {
    if (i == 0) { if (j == 1) return k - 2; if (j == 2) return k == 3 ? 3 : 4; return 5; }
    if (i == 1) { if (j == 2) return k == 3 ? 6 : 7; return 8; }
    return 9;
}
static inline void normal4(const int *T, const int *d, int *N) {  /* Q_ijkl = T_ijk d_l - T_ijl d_k + T_ikl d_j - T_jkl d_i */
    static const int Q[5][4] = {{1, 2, 3, 4}, {0, 2, 3, 4}, {0, 1, 3, 4}, {0, 1, 2, 4}, {0, 1, 2, 3}};  /* without m */
    for (int m = 0; m < 5; m++) {
        int i = Q[m][0], j = Q[m][1], k = Q[m][2], l = Q[m][3];
        int v = add[sub[mul[T[tidx(i, j, k)]][d[l]]][mul[T[tidx(i, j, l)]][d[k]]]][sub[mul[T[tidx(i, k, l)]][d[j]]][mul[T[tidx(j, k, l)]][d[i]]]];
        N[m] = m & 1 ? sub[0][v] : v;
    }
}
static inline int dot5(const int *N, const int *e) {
    return add[add[add[mul[N[0]][e[0]]][mul[N[1]][e[1]]]][add[mul[N[2]][e[2]]][mul[N[3]][e[3]]]]][mul[N[4]][e[4]]];
}

static int dep6(uint32_t p, uint32_t A, uint32_t B, uint32_t C, uint32_t D, uint32_t E) {  /* six points on one hyperplane */
    int a[5], b[5], c[5], d[5], e[5], W2[10], W3[10], N[5];
    dir(A, p, a); dir(B, p, b); dir(C, p, c); dir(D, p, d); dir(E, p, e);
    wedge2(a, b, W2); wedge3(W2, c, W3); normal4(W3, d, N);
    return dot5(N, e) == 0;
}

static int k, G, THR, PLR;         /* other columns; cyclic rows; bucket size listed directly; rows with plane lists */
static clock_t T0;
static uint32_t *H[MAXN], cand[MAXN];  /* cyclic rows: point of other column i (column i + 1); column 0's point */
static uint32_t *PL[MAXN];         /* bucketed rows: the NPH hyperplanes through each other column's direction */
static uint64_t *S; static long nS;  /* five-sets of other columns that fail with column 0 in every cyclic row */

struct ctx {
    uint32_t *ent[MAXN]; int *CNT[MAXN], *OFF[MAXN], *TCH[MAXN];
    long entcap[MAXN];
    int (*dv)[5];
    uint64_t *S; long nS, capS;
    uint32_t *scratch;             /* plane list of a column in a row without a stored list */
};

static void keep(struct ctx *X, int a, int b, int c, int d, int e) {
    if (X->nS == X->capS) { X->capS = X->capS ? X->capS * 2 : 1 << 12; X->S = realloc(X->S, sizeof(uint64_t) * X->capS); }
    X->S[X->nS++] = (uint64_t)a << 48 | (uint64_t)b << 36 | (uint64_t)c << 24 | (uint64_t)d << 12 | (uint64_t)e;
}

static void leaf(struct ctx *X, const int *L, int len, int r0) {
    if (r0 >= G) {
        for (int a = 0; a < len; a++) for (int b = a + 1; b < len; b++) for (int c = b + 1; c < len; c++)
            for (int d = c + 1; d < len; d++) for (int e = d + 1; e < len; e++) keep(X, L[a], L[b], L[c], L[d], L[e]);
        return;
    }
    int (*dv)[5] = X->dv;
    for (int x = 0; x < len; x++) dir(H[r0][L[x]], cand[r0], dv[x]);
    for (int a = 0; a + 4 < len; a++)  /* bounds leave room for the later members */
        for (int b = a + 1; b + 3 < len; b++) {
            int W2[10];
            wedge2(dv[a], dv[b], W2);
            for (int c = b + 1; c + 2 < len; c++) {
                int W3[10];
                wedge3(W2, dv[c], W3);
                for (int d = c + 1; d + 1 < len; d++) {
                    int N[5];
                    normal4(W3, dv[d], N);
                    for (int e = d + 1; e < len; e++) {
                        if (dot5(N, dv[e])) continue;
                        int ok = 1, A = L[a], B = L[b], C = L[c], D = L[d], E = L[e];
                        for (int r = r0 + 1; r < G && ok; r++) ok = dep6(cand[r], H[r][A], H[r][B], H[r][C], H[r][D], H[r][E]);
                        if (ok) keep(X, A, B, C, D, E);
                    }
                }
            }
        }
}

static const uint32_t *planes(struct ctx *X, int r, int x) {  /* hyperplanes through other column x's direction */
    if (r < PLR) return PL[r] + (size_t)x * NPH;
    int v[5];
    dir(H[r][x], cand[r], v);
    if (!v[0] && !v[1] && !v[2] && !v[3] && !v[4]) { X->scratch[0] = WILD; return X->scratch; }
    hyps(v, X->scratch);
    return X->scratch;
}

static int split(struct ctx *X, int lev, const int *L, int len) {  /* buckets of L in row lev; returns planes touched */
    int *cnt = X->CNT[lev], *off = X->OFF[lev], *tch = X->TCH[lev], nt = 0;
    long total = 0;
    for (int x = 0; x < len; x++) {
        const uint32_t *pl = planes(X, lev, L[x]);
        if (pl[0] == WILD) { for (int l = 0; l < NN; l++) if (cnt[l]++ == 0) tch[nt++] = l; total += NN; }
        else { for (int j = 0; j < NPH; j++) if (cnt[pl[j]]++ == 0) tch[nt++] = (int)pl[j]; total += NPH; }
    }
    if (total > X->entcap[lev]) { X->entcap[lev] = total; X->ent[lev] = realloc(X->ent[lev], sizeof(uint32_t) * total); }
    uint32_t *e = X->ent[lev];
    int s = 0;
    for (int t = 0; t < nt; t++) { off[tch[t]] = s; s += cnt[tch[t]]; }
    for (int x = 0; x < len; x++) {
        const uint32_t *pl = planes(X, lev, L[x]);
        if (pl[0] == WILD) for (int l = 0; l < NN; l++) e[off[l]++] = (uint32_t)L[x];
        else for (int j = 0; j < NPH; j++) e[off[pl[j]]++] = (uint32_t)L[x];
    }
    return nt;
}

static void bucket(struct ctx *X, int lev, const int *L, int len) {  /* L ascending; every bucket keeps the order */
    if (lev == G || len <= THR) { leaf(X, L, len, lev); return; }
    int nt = split(X, lev, L, len), *cnt = X->CNT[lev], *off = X->OFF[lev], *tch = X->TCH[lev];
    const int *e = (const int *)X->ent[lev];
    for (int t = 0; t < nt; t++) {
        int l = tch[t], c = cnt[l];
        if (c >= 5) bucket(X, lev + 1, e + off[l] - c, c);
    }
    for (int t = 0; t < nt; t++) cnt[tch[t]] = 0;
}

static struct ctx *CX;
static int nthreads, top_nt, top_next;

static void *worker(void *arg) {
    struct ctx *X = arg, *X0 = &CX[0];
    for (;;) {
        int t = __sync_fetch_and_add(&top_next, 1);
        if (t >= top_nt) return NULL;
        int l = X0->TCH[0][t], c = X0->CNT[0][l];
        if (c >= 5) bucket(X, 1, (const int *)X0->ent[0] + X0->OFF[0][l] - c, c);
        if ((t + 1) % (top_nt / 10 + 1) == 0)
            fprintf(stderr, "  %d of %d row-0 hyperplanes, %.0f s\n", t + 1, top_nt, (double)(clock() - T0) / CLOCKS_PER_SEC);
    }
}

static void enumerate(const int *L, int len) {
    for (int w = 0; w < nthreads; w++) CX[w].nS = 0;
    if (G == 0 || len <= THR) leaf(&CX[0], L, len, 0);
    else {
        top_nt = split(&CX[0], 0, L, len);
        top_next = 0;
        pthread_t th[64];
        for (int w = 1; w < nthreads; w++) pthread_create(&th[w], NULL, worker, &CX[w]);
        worker(&CX[0]);
        for (int w = 1; w < nthreads; w++) pthread_join(th[w], NULL);
        for (int t = 0; t < top_nt; t++) CX[0].CNT[0][CX[0].TCH[0][t]] = 0;
    }
    nS = 0;
    for (int w = 0; w < nthreads; w++) nS += CX[w].nS;
    S = realloc(S, sizeof(uint64_t) * (nS + 1));
    long o = 0;
    for (int w = 0; w < nthreads; w++) { memcpy(S + o, CX[w].S, sizeof(uint64_t) * CX[w].nS); o += CX[w].nS; }
}

static int f5c[5];                 /* GF(q^5) = GF(q)[x]/(x^5 + f4 x^4 + ... + f0) */
static uint32_t *ex;               /* powers of a primitive element */
static long Qm1;

static uint32_t enc(const int *c) { uint32_t v = 0; for (int i = 0; i < 5; i++) v = v * (uint32_t)q + (uint32_t)c[i]; return v; }

static uint32_t timesx(uint32_t a) {  /* x^5 = -(f0 + f1 x + ... + f4 x^4) */
    int c[5], o[5];
    for (int i = 0; i < 5; i++) c[i] = cx[i][a];
    o[0] = sub[0][mul[c[4]][f5c[0]]];
    for (int i = 1; i < 5; i++) o[i] = sub[c[i - 1]][mul[c[4]][f5c[i]]];
    return enc(o);
}

static uint32_t fmul(uint32_t a, uint32_t b) {  /* Horner over b's coefficients, highest first */
    uint32_t r = 0;
    for (int i = 4; i >= 0; i--) {
        r = timesx(r);
        int t = cx[i][b], o[5];
        for (int j = 0; j < 5; j++) o[j] = add[cx[j][r]][mul[t][cx[j][a]]];
        r = enc(o);
    }
    return r;
}

static uint32_t fpow(uint32_t a, long e) {
    int one[5] = {1, 0, 0, 0, 0};
    uint32_t r = enc(one);
    while (e) { if (e & 1) r = fmul(r, a); a = fmul(a, a); e >>= 1; }
    return r;
}

static int irreducible5(void) {  /* no root and no monic quadratic factor */
    for (int a = 0; a < q; a++) {
        int v = 1;
        for (int i = 4; i >= 0; i--) v = add[mul[v][a]][f5c[i]];
        if (!v) return 0;
    }
    for (int b = 0; b < q; b++)
        for (int c = 0; c < q; c++) {
            int r[6] = {f5c[0], f5c[1], f5c[2], f5c[3], f5c[4], 1};
            for (int d = 5; d >= 2; d--) {
                int l = r[d];
                if (!l) continue;
                r[d] = 0; r[d - 1] = sub[r[d - 1]][mul[l][b]]; r[d - 2] = sub[r[d - 2]][mul[l][c]];
            }
            if (!r[0] && !r[1]) return 0;
        }
    return 1;
}

static void build_field(void) {
    do { for (int i = 0; i < 5; i++) f5c[i] = (int)(rnd() % q); } while (!irreducible5());
    Qm1 = (long)P - 1;
    long pr[16], m = Qm1;
    int np = 0;
    for (long d = 2; d * d <= m; d++) if (m % d == 0) { pr[np++] = d; while (m % d == 0) m /= d; }
    if (m > 1) pr[np++] = m;
    int onev[5] = {1, 0, 0, 0, 0};
    uint32_t g, one = enc(onev);
    for (;;) {
        g = (uint32_t)(1 + rnd() % (uint64_t)(P - 1));
        int ok = 1;
        for (int i = 0; i < np && ok; i++) ok = fpow(g, Qm1 / pr[i]) != one;
        if (ok) break;
    }
    ex = malloc(sizeof(uint32_t) * Qm1);
    ex[0] = one;
    for (long i = 1; i < Qm1; i++) ex[i] = fmul(ex[i - 1], g);
    if (fmul(ex[Qm1 - 1], g) != one) { fprintf(stderr, "GF(q^5) is wrong\n"); exit(3); }
}

static long gcdl(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }
static long rclass(long e) { long b = e, x = e; for (int i = 1; i < 5; i++) { x = x * q % Qm1; if (x < b) b = x; } return b; }
static long used[MAXN]; static int nused;

static long pick(int K) {  /* a random exponent: order of gamma^e at least K, Frobenius class not used yet */
    for (;;) {
        long e = 1 + (long)(rnd() % (uint64_t)(Qm1 - 1));
        if (Qm1 / gcdl(e, Qm1) < K) continue;
        long c = rclass(e);
        int dup = 0;
        for (int i = 0; i < nused; i++) dup |= used[i] == c;
        if (!dup) return e;
    }
}

static int covered(uint32_t *const *R, int nr, long s0, uint64_t t) {  /* columns s0 + {0, a+1, ..., e+1} independent in
                                                                          one of the nr rows R? */
    long c[5];
    for (int i = 0; i < 5; i++) c[i] = s0 + (long)(t >> (48 - 12 * i) & 0xFFF) + 1;
    for (int r = 0; r < nr; r++) if (!dep6(R[r][s0], R[r][c[0]], R[r][c[1]], R[r][c[2]], R[r][c[3]], R[r][c[4]])) return 1;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: cphf6c q n seconds seed K [C]\n"); return 2; }
    q = atoi(argv[1]); n = atoi(argv[2]);
    double secs = atof(argv[3]);
    rng = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 0xD1B54A32D192ED03ULL;
    int K = atoi(argv[5]);
    if (q > MAXQ || n > MAXN || n < 4 || !field(q)) { fprintf(stderr, "q must be a supported prime power <= %d, 4 <= n <= %d\n", MAXQ, MAXN); return 2; }
    if (K < 7 || K > MAXK) { fprintf(stderr, "need 7 <= K <= %d\n", MAXK); return 2; }
    geometry();
    build_field();
    double pbad = 1;
    for (int i = 0; i < 5; i++) pbad *= 1 - pow(q, i - 5);
    pbad = 1 - pbad;
    double sets = (double)(K - 1) * (K - 2) * (K - 3) * (K - 4) * (K - 5) / 120;
    int C = argc > 6 ? atoi(argv[6]) : (int)ceil(log(sets / 1000) / -log(pbad));
    if (C < 1 || C > n - 2) { fprintf(stderr, "need 1 <= C <= n - 2 (C %d)\n", C); return 2; }
    long period = Qm1 / (q - 1);
    fprintf(stderr, "GF(%d^5) mod x^5 + %d x^4 + %d x^3 + %d x^2 + %d x + %d; GF(q) reached every %ld; %.3g five-sets with column 0; "
            "%d cyclic rows (about %.3g left by chance), %d random\n", q, f5c[4], f5c[3], f5c[2], f5c[1], f5c[0], period, sets, C,
            sets * pow(pbad, C), n - C);
    uint32_t *A[MAXN];
    for (int r = 0; r < n; r++) { A[r] = malloc(sizeof(uint32_t) * K); H[r] = malloc(sizeof(uint32_t) * K); }
    THR = getenv("CPHF_THR") ? atoi(getenv("CPHF_THR")) : (int)(1.2 * pow(120.0 * NPH, 0.25));
    PLR = 0;  /* rows whose plane lists are stored: those the bucketing will usually reach */
    for (double s = K; s > THR && PLR < C; s /= q) PLR++;
    nthreads = getenv("CPHF_THREADS") ? atoi(getenv("CPHF_THREADS")) : 6;
    if (nthreads < 1) nthreads = 1;
    if (nthreads > 64) nthreads = 64;
    CX = calloc(nthreads, sizeof(struct ctx));
    for (int w = 0; w < nthreads; w++) {
        struct ctx *X = &CX[w];
        for (int r = 0; r < n; r++) { X->CNT[r] = calloc(NN, sizeof(int)); X->OFF[r] = malloc(sizeof(int) * NN); X->TCH[r] = malloc(sizeof(int) * NN); }
        X->dv = malloc(sizeof(int[5]) * K);
        X->scratch = malloc(sizeof(uint32_t) * (NPH > 1 ? NPH : 1));
    }
    for (int r = 0; r < PLR; r++) PL[r] = malloc(sizeof(uint32_t) * (size_t)K * NPH);
    int *L = malloc(sizeof(int) * K);
    long *ush = NULL, nu = 0, capu = 0, ex_r[MAXN];
    T0 = clock();
    for (int att = 1; (double)(clock() - T0) / CLOCKS_PER_SEC < secs; att++) {
        nused = 0;
        G = C;
        for (int r = 0; r < C; r++) {
            ex_r[r] = pick(K);
            used[nused++] = rclass(ex_r[r]);
            for (int j = 0; j < K; j++) A[r][j] = ex[ex_r[r] * j % Qm1];
            for (int j = 1; j < K; j++) H[r][j - 1] = A[r][j];
            cand[r] = A[r][0];
        }
        k = K - 1;
        for (int r = 0; r < PLR; r++)
            for (int x = 0; x < k; x++) {
                int v[5];
                dir(H[r][x], cand[r], v);
                uint32_t *o = PL[r] + (size_t)x * NPH;
                if (!v[0] && !v[1] && !v[2] && !v[3] && !v[4]) { o[0] = WILD; continue; }
                if (hyps(v, o) != NPH) { fprintf(stderr, "PG(4,q) incidence is wrong\n"); return 3; }
            }
        for (int i = 0; i < k; i++) L[i] = i;
        enumerate(L, k);
        double shifts = 0;
        for (long i = 0; i < nS; i++) shifts += K - 1 - (double)(S[i] & 0xFFF);  /* shifts s with s + last column < K */
        fprintf(stderr, "attempt %d: %ld five-sets with column 0 fail in all %d cyclic rows, %.4g shifted sets, %.0f s\n",
                att, nS, C, shifts, (double)(clock() - T0) / CLOCKS_PER_SEC);
        int ok = 0;
        for (int tries = 0; tries < 50 && !ok && (double)(clock() - T0) / CLOCKS_PER_SEC < secs; tries++) {
            for (int r = C; r < n - 1; r++) for (int j = 0; j < K; j++) A[r][j] = (uint32_t)(rnd() % P);
            nu = 0;
            for (long i = 0; i < nS; i++) {
                long top = (long)(S[i] & 0xFFF) + 1;
                for (long s0 = 0; s0 + top < K; s0++)
                    if (!covered(A + C, n - 1 - C, s0, S[i])) {
                        if (2 * nu + 2 > capu) { capu = capu ? capu * 2 : 1 << 16; ush = realloc(ush, sizeof(long) * capu); }
                        ush[2 * nu] = i; ush[2 * nu + 1] = s0; nu++;
                    }
            }
            fprintf(stderr, "  %ld shifted sets left after %d random rows, %.0f s\n", nu, n - 1 - C, (double)(clock() - T0) / CLOCKS_PER_SEC);
            for (int tr = 0; tr < 2000 && !ok; tr++) {
                for (int j = 0; j < K; j++) A[n - 1][j] = (uint32_t)(rnd() % P);
                ok = 1;
                for (long u = 0; u < nu && ok; u++) ok = covered(A + n - 1, 1, ush[2 * u + 1], S[ush[2 * u]]);
            }
            if (!ok) fprintf(stderr, "  no last row covers them\n");
        }
        if (!ok) continue;
        printf("best k %d (q %d, n %d, t 6, cyclic %d, %.0f s)\n", K, q, n, C, (double)(clock() - T0) / CLOCKS_PER_SEC);
        printf("# GF(%d^5) mod x^5 + %d x^4 + %d x^3 + %d x^2 + %d x + %d; cyclic rows gamma^(e j), gamma = point %u, e =",
               q, f5c[4], f5c[3], f5c[2], f5c[1], f5c[0], ex[1]);
        for (int r = 0; r < C; r++) printf(" %ld", ex_r[r]);
        printf("; rows %d..%d random\n", C, n - 1);
        for (int r = 0; r < n; r++) {
            for (int j = 0; j < K; j++) printf(j ? " %u" : "%u", A[r][j]);
            printf("\n");
        }
        return 0;
    }
    printf("best k 0 (q %d, n %d, t 6, cyclic %d, %.0f s)\n", q, n, C, (double)(clock() - T0) / CLOCKS_PER_SEC);
    return 1;
}
