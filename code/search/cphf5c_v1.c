/* Strength-5 Sherwood CPHFs with 10,000 columns, part cyclic: SCPHF(n; K, q^4, 5) whose first C rows are affine
   progressions v, T v, T^2 v, ..., T^(K-1) v of points of AG(4,q), each under an invertible affine map T of its own,
   and whose other rows are random. Applying T^s to a cyclic row keeps every set of points on or off a hyperplane, so
   columns j1 < ... < j5 fail in all cyclic rows exactly when 0, j2 - j1, ..., j5 - j1 do: those sets are the shifts
   of the few sets holding column 0 that fail in all cyclic rows, found as in cphf5m.c (the other columns bucketed by
   the planes of PG(3,q) through their directions from column 0's point, row by row, the quadruples sharing a bucket
   filtered through the remaining cyclic rows), and only their shifts need the random rows. Two kinds of cyclic row,
   because each alone has sets it can never cover:
     type 1: a^j in GF(q^4) = GF(q)[x]/(f) (basis 1, x, x^2, x^3), a of order at least K. Its powers a^(mj), m the
       order of a over that of GF(q^2), lie in GF(q^2), a plane through 0, so any set with three columns at multiples
       of m (q^2 + 1 or half of it) fails in every type-1 row.
     type 2: (s^j, j c) in GF(q^3) x GF(q), s of GF(q^3) = GF(q)[x]/(g), c in GF(q)*, order lcm(order of s, p) at
       least K (q = 11, 13, 17, 19, 23, 25 for K = 10,000). Columns congruent mod p share the last coordinate, so five
       of them fail in every type-2 row; type-1 rows cover those and type-2 rows cover the type-1 sets.
   Neither kind alone, nor both together, covers everything: sets like {0, a, b, a + b, x} with a = 0 mod p and b a
   multiple of the type-2 period have four columns on one plane in every type-2 row (a trapezoid) and also fail in
   type-1 rows. Hence the random rows: rows 0..C-1 are random cyclic rows of the two types (alternating, order at
   least K, Frobenius classes distinct), giving the list B of sets holding column 0 that fail in all of them; rows
   C..n-2 are random points, checked against every shift of every set in B; the last row is redrawn until it covers
   every shifted set the others leave, and the random rows are redrawn until that works or time runs out.
   Prints "best k K (q Q, n N, t 5, cyclic C, S s)" (best k 0 when it failed), a comment line with the fields and the
   cyclic rows, then the array (n lines of point ids ((x q + y) q + z) q + w).
   The bucketing runs on CPHF_THREADS threads (default 6), sharing out the row-0 planes.
   cc -O3 -o cphf5c cphf5c.c -lm -lpthread && ./cphf5c q n seconds seed K [C] (CPHF_THR sets THR) */
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 25
#define MAXN 40
#define ALL 0xFFFFFFFFu

static int q, P, n, NN, NP, NPL;
static int add[MAXQ][MAXQ], mul[MAXQ][MAXQ], sub[MAXQ][MAXQ], inv[MAXQ];
static uint8_t *px, *py, *pz, *pw;
static uint8_t (*nv)[4];           /* the NN points of PG(3,q), first nonzero coordinate 1; also the planes' normals */
static int *dcls;                  /* direction class of each difference vector (as a point id), -1 for zero */
static int *ptpl;                  /* the NP = q^2 + q + 1 planes of PG(3,q) through each point, NP per point */
static uint32_t *H[MAXN];
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

static int dirclass(int a, int b, int c, int d) {  /* class of a nonzero vector: first nonzero coordinate 1 */
    if (a) { int s = inv[a]; return (mul[b][s] * q + mul[c][s]) * q + mul[d][s]; }
    if (b) { int s = inv[b]; return q * q * q + mul[c][s] * q + mul[d][s]; }
    if (c) return q * q * q + q * q + mul[d][inv[c]];
    return q * q * q + q * q + q;
}


/* Normal of the span of u, v, s (generalised cross product): N_i = (-1)^i det of [u; v; s] without column i, so
   N . x = det[x; u; v; s]. With Q_ab = s_a u_b - s_b u_a, that minor is v_j Q_kl - v_k Q_jl + v_l Q_jk. */
#define SPAN_NORMAL(u0, u1, u2, u3, v0, v1, v2, v3, s0, s1, s2, s3, N0, N1, N2, N3) do { \
    int Q01 = sub[mul[s0][u1]][mul[s1][u0]], Q02 = sub[mul[s0][u2]][mul[s2][u0]], Q03 = sub[mul[s0][u3]][mul[s3][u0]]; \
    int Q12 = sub[mul[s1][u2]][mul[s2][u1]], Q13 = sub[mul[s1][u3]][mul[s3][u1]], Q23 = sub[mul[s2][u3]][mul[s3][u2]]; \
    N0 = add[sub[mul[v1][Q23]][mul[v2][Q13]]][mul[v3][Q12]]; \
    N1 = sub[0][add[sub[mul[v0][Q23]][mul[v2][Q03]]][mul[v3][Q02]]]; \
    N2 = add[sub[mul[v0][Q13]][mul[v1][Q03]]][mul[v3][Q01]]; \
    N3 = sub[0][add[sub[mul[v0][Q12]][mul[v1][Q02]]][mul[v2][Q01]]]; } while (0)

static int onehyp(uint32_t A, uint32_t B, uint32_t C, uint32_t D, uint32_t p) {  /* det(B-A, C-A, D-A, p-A) == 0 */
    int a0 = px[A], a1 = py[A], a2 = pz[A], a3 = pw[A], N0, N1, N2, N3;
    SPAN_NORMAL(sub[px[B]][a0], sub[py[B]][a1], sub[pz[B]][a2], sub[pw[B]][a3],
                sub[px[C]][a0], sub[py[C]][a1], sub[pz[C]][a2], sub[pw[C]][a3],
                sub[px[D]][a0], sub[py[D]][a1], sub[pz[D]][a2], sub[pw[D]][a3], N0, N1, N2, N3);
    return add[add[mul[N0][sub[px[p]][a0]]][mul[N1][sub[py[p]][a1]]]][add[mul[N2][sub[pz[p]][a2]]][mul[N3][sub[pw[p]][a3]]]] == 0;
}

static void geometry(void) {
    P = q * q * q * q; NN = q * q * q + q * q + q + 1; NP = q * q + q + 1; NPL = NN * q;
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
            int s = add[add[mul[nv[l][0]][nv[d][0]]][mul[nv[l][1]][nv[d][1]]]][add[mul[nv[l][2]][nv[d][2]]][mul[nv[l][3]][nv[d][3]]]];
            if (!s) { if (j == NP) { fprintf(stderr, "PG(3,q) incidence is wrong\n"); exit(3); } ptpl[(size_t)d * NP + j++] = l; }
        }
        if (j != NP) { fprintf(stderr, "PG(3,q) incidence is wrong\n"); exit(3); }
    }
}

static int k, G, THR;              /* columns; cyclic rows; bucket size listed directly */
static clock_t T0;
static uint32_t cand[MAXN];
static uint64_t *S; static long nS;  /* sets holding column 0 that fail in every cyclic row (columns minus 1) */

struct ctx {  /* one thread's scratch, one set per level, and the quadruples it keeps */
    int *ent[MAXN], *cls[MAXN], *CNT[MAXN], *OFF[MAXN], *TCH[MAXN];
    long entcap[MAXN];
    int *d0, *d1, *d2, *d3;          /* leaf: differences from the first column of a quadruple */
    uint64_t *S; long nS, capS;
};

static void keep(struct ctx *X, int a, int b, int c, int d) {
    if (X->nS == X->capS) { X->capS = X->capS ? X->capS * 2 : 1 << 12; X->S = realloc(X->S, sizeof(uint64_t) * X->capS); }
    X->S[X->nS++] = (uint64_t)a << 48 | (uint64_t)b << 32 | (uint64_t)c << 16 | (uint64_t)d;
}

static void leaf(struct ctx *X, const int *L, int len, int r0) {  /* quadruples of L (on one hyperplane with column
                                                                     0 in rows 0..r0-1), filtered through rows r0..G-1 */
    if (r0 >= G) {
        for (int x = 0; x < len; x++) for (int y = x + 1; y < len; y++) for (int z = y + 1; z < len; z++)
            for (int t = z + 1; t < len; t++) keep(X, L[x], L[y], L[z], L[t]);
        return;
    }
    const uint32_t *R = H[r0];
    uint32_t p = cand[r0];
    int *d0 = X->d0, *d1 = X->d1, *d2 = X->d2, *d3 = X->d3;
    for (int x = 0; x < len; x++) {
        int a = L[x];
        uint32_t A = R[a];
        int a0 = px[A], a1 = py[A], a2 = pz[A], a3 = pw[A];
        int w0 = sub[px[p]][a0], w1 = sub[py[p]][a1], w2 = sub[pz[p]][a2], w3 = sub[pw[p]][a3];
        for (int z = x + 1; z < len; z++) {
            uint32_t C = R[L[z]];
            d0[z] = sub[px[C]][a0]; d1[z] = sub[py[C]][a1]; d2[z] = sub[pz[C]][a2]; d3[z] = sub[pw[C]][a3];
        }
        for (int y = x + 1; y < len; y++) {
            int u0 = d0[y], u1 = d1[y], u2 = d2[y], u3 = d3[y];
            /* with s = p - A fixed: Q_ab = w_a u_b - w_b u_a, then per C the normal of span(u, v, w) */
            int Q01 = sub[mul[w0][u1]][mul[w1][u0]], Q02 = sub[mul[w0][u2]][mul[w2][u0]], Q03 = sub[mul[w0][u3]][mul[w3][u0]];
            int Q12 = sub[mul[w1][u2]][mul[w2][u1]], Q13 = sub[mul[w1][u3]][mul[w3][u1]], Q23 = sub[mul[w2][u3]][mul[w3][u2]];
            for (int z = y + 1; z < len; z++) {
                int v0 = d0[z], v1 = d1[z], v2 = d2[z], v3 = d3[z];
                int N0 = add[sub[mul[v1][Q23]][mul[v2][Q13]]][mul[v3][Q12]];
                int N1 = sub[0][add[sub[mul[v0][Q23]][mul[v2][Q03]]][mul[v3][Q02]]];
                int N2 = add[sub[mul[v0][Q13]][mul[v1][Q03]]][mul[v3][Q01]];
                int N3 = sub[0][add[sub[mul[v0][Q12]][mul[v1][Q02]]][mul[v2][Q01]]];
                int b = L[y], c = L[z];
                for (int t = z + 1; t < len; t++) {  /* det(D - A, B - A, C - A, p - A) = N . (D - A) */
                    if (add[add[mul[N0][d0[t]]][mul[N1][d1[t]]]][add[mul[N2][d2[t]]][mul[N3][d3[t]]]]) continue;
                    int d = L[t], ok = 1;
                    for (int r = r0 + 1; r < G && ok; r++) ok = onehyp(H[r][a], H[r][b], H[r][c], H[r][d], cand[r]);
                    if (ok) keep(X, a, b, c, d);
                }
            }
        }
    }
}

static int split(struct ctx *X, int lev, const int *L, int len) {  /* buckets of L in row lev (ent, OFF, TCH of the
                                                                      level); returns how many planes were touched */
    uint32_t p = cand[lev];
    int *cnt = X->CNT[lev], *off = X->OFF[lev], *tch = X->TCH[lev], *cl = X->cls[lev], nt = 0;
    long total = 0;
    for (int x = 0; x < len; x++) {
        uint32_t A = H[lev][L[x]];
        int d = dcls[((sub[px[A]][px[p]] * q + sub[py[A]][py[p]]) * q + sub[pz[A]][pz[p]]) * q + sub[pw[A]][pw[p]]];
        cl[x] = d;
        if (d < 0) { for (int l = 0; l < NN; l++) if (cnt[l]++ == 0) tch[nt++] = l; total += NN; }
        else {
            const int *pl = ptpl + (size_t)d * NP;
            for (int j = 0; j < NP; j++) if (cnt[pl[j]]++ == 0) tch[nt++] = pl[j];
            total += NP;
        }
    }
    if (total > X->entcap[lev]) { X->entcap[lev] = total; X->ent[lev] = realloc(X->ent[lev], sizeof(int) * total); }
    int *e = X->ent[lev], s = 0;
    for (int t = 0; t < nt; t++) { off[tch[t]] = s; s += cnt[tch[t]]; }
    for (int x = 0; x < len; x++) {
        int d = cl[x];
        if (d < 0) for (int l = 0; l < NN; l++) e[off[l]++] = L[x];
        else { const int *pl = ptpl + (size_t)d * NP; for (int j = 0; j < NP; j++) e[off[pl[j]]++] = L[x]; }
    }
    return nt;
}

static void bucket(struct ctx *X, int lev, const int *L, int len) {  /* L ascending; every bucket keeps the order */
    if (lev == G || len <= THR) { leaf(X, L, len, lev); return; }
    int nt = split(X, lev, L, len), *cnt = X->CNT[lev], *off = X->OFF[lev], *tch = X->TCH[lev], *e = X->ent[lev];
    for (int t = 0; t < nt; t++) {
        int l = tch[t], c = cnt[l];
        if (c >= 4) bucket(X, lev + 1, e + off[l] - c, c);
    }
    for (int t = 0; t < nt; t++) cnt[tch[t]] = 0;
}

static struct ctx *CX;
static int nthreads, top_nt, top_next;  /* row-0 planes, shared out by an atomic counter */

static void *worker(void *arg) {
    struct ctx *X = arg, *X0 = &CX[0];
    for (;;) {
        int t = __sync_fetch_and_add(&top_next, 1);
        if (t >= top_nt) return NULL;
        int l = X0->TCH[0][t], c = X0->CNT[0][l];
        if (c >= 4) bucket(X, 1, X0->ent[0] + X0->OFF[0][l] - c, c);
        if ((t + 1) % (top_nt / 10 + 1) == 0)
            fprintf(stderr, "  %d of %d row-0 planes, %.0f s\n", t + 1, top_nt, (double)(clock() - T0) / CLOCKS_PER_SEC);
    }
}

static void enumerate(const int *L, int len) {  /* every set holding column 0 that fails in all G cyclic rows -> S */
    for (int w = 0; w < nthreads; w++) CX[w].nS = 0;
    if (G == 0 || len <= THR) { leaf(&CX[0], L, len, 0); }
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

static int f4c[4], f3c[3];         /* GF(q^4) = GF(q)[x]/(x^4 + f3 x^3 + ... + f0), GF(q^3) = GF(q)[x]/(x^3 + ... + g0) */
static uint32_t *ex, *ex3;         /* powers of a primitive element of each */
static long Qm1, Q3m1;
static int pchar;                  /* the characteristic: j c in GF(q) repeats with period p */

static uint32_t enc(int c0, int c1, int c2, int c3) { return (uint32_t)(((c0 * q + c1) * q + c2) * q + c3); }

static uint32_t timesx(uint32_t a, int deg, const int *f) {  /* x a modulo the monic f of degree deg (3 or 4) */
    int c[4] = {px[a], py[a], pz[a], pw[a]}, top = c[deg - 1], o[4] = {0, 0, 0, 0};
    o[0] = sub[0][mul[top][f[0]]];
    for (int i = 1; i < deg; i++) o[i] = sub[c[i - 1]][mul[top][f[i]]];
    return enc(o[0], o[1], o[2], o[3]);
}

static uint32_t fmul(uint32_t a, uint32_t b, int deg, const int *f) {  /* Horner over b's coefficients, highest first */
    int bc[4] = {px[b], py[b], pz[b], pw[b]};
    uint32_t r = 0;
    for (int i = deg - 1; i >= 0; i--) {
        r = timesx(r, deg, f);
        int t = bc[i];
        r = enc(add[px[r]][mul[t][px[a]]], add[py[r]][mul[t][py[a]]], add[pz[r]][mul[t][pz[a]]], add[pw[r]][mul[t][pw[a]]]);
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
        for (int i = deg - 1; i >= 0; i--) v = add[mul[v][a]][f[i]];
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
                r[d] = 0; r[d - 1] = sub[r[d - 1]][mul[l][b]]; r[d - 2] = sub[r[d - 2]][mul[l][c]];
            }
            if (!r[0] && !r[1]) return 0;
        }
    return 1;
}

static uint32_t *powers(int deg, const int *f, long order) {  /* powers of a primitive element of GF(q^deg) */
    long pr[16], m = order;
    int np = 0;
    for (long d = 2; d * d <= m; d++) if (m % d == 0) { pr[np++] = d; while (m % d == 0) m /= d; }
    if (m > 1) pr[np++] = m;
    uint32_t g, one = enc(1, 0, 0, 0);
    long size = 1;
    for (int i = 0; i < deg; i++) size *= q;
    for (;;) {  /* no power order/p is 1; elements are the ids below q^deg shifted into the first deg coordinates */
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

static void build_fields(void) {
    do { for (int i = 0; i < 4; i++) f4c[i] = (int)(rnd() % q); } while (!irreducible4());
    do { for (int i = 0; i < 3; i++) f3c[i] = (int)(rnd() % q); } while (!noroot(3, f3c));
    Qm1 = (long)P - 1; Q3m1 = (long)q * q * q - 1;
    ex = powers(4, f4c, Qm1);
    ex3 = powers(3, f3c, Q3m1);
    pchar = 2;
    while (q % pchar) pchar++;
}

static long gcdl(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }

struct row { int type, c; long e; };

static long rorder(const struct row *R) {
    if (R->type == 1) return Qm1 / gcdl(R->e, Qm1);
    long o = Q3m1 / gcdl(R->e, Q3m1);
    return o / gcdl(o, pchar) * pchar;
}

static long rclass(const struct row *R) {  /* rows a^e and a^(eq) differ by the Frobenius map, a linear one */
    long m = R->type == 1 ? Qm1 : Q3m1, b = R->e, x = R->e;
    for (int i = 1; i < (R->type == 1 ? 4 : 3); i++) { x = x * q % m; if (x < b) b = x; }
    return b * 2 + R->type - 1;
}

static inline uint32_t point(const struct row *R, long j) {
    if (R->type == 1) return ex[R->e * j % Qm1];
    uint32_t u = ex3[R->e * j % Q3m1];  /* GF(q^3) element in the first three coordinates, j c in the last */
    return u + (uint32_t)mul[j % pchar][R->c];
}

static long used[MAXN]; static int nused;

static struct row pick(int K, int type) {  /* a random row of the type: order at least K, class not used yet */
    struct row R;
    R.type = type;
    for (;;) {
        R.e = 1 + (long)(rnd() % (uint64_t)((type == 1 ? Qm1 : Q3m1) - 1));
        R.c = 1 + (int)(rnd() % (q - 1));
        if (rorder(&R) < K) continue;
        long c = rclass(&R);
        int dup = 0;
        for (int i = 0; i < nused; i++) dup |= used[i] == c;
        if (!dup) return R;
    }
}

static void fillrow(int r, const struct row *R, int K) {  /* old column i is column i + 1; column 0 is the new point */
    for (int j = 1; j < K; j++) H[r][j - 1] = point(R, j);
    cand[r] = point(R, 0);
}


static int covered(uint32_t *const *R, int nr, long s0, uint64_t t) {  /* columns s0 + {0, a, b, c, d} independent in
                                                                          one of the nr rows R? (t holds a-1, ..., d-1) */
    long a = s0 + (long)(t >> 48) + 1, b = s0 + (long)(t >> 32 & 0xFFFF) + 1, c = s0 + (long)(t >> 16 & 0xFFFF) + 1, d = s0 + (long)(t & 0xFFFF) + 1;
    for (int r = 0; r < nr; r++) if (!onehyp(R[r][a], R[r][b], R[r][c], R[r][d], R[r][s0])) return 1;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: cphf5c q n seconds seed K [C]\n"); return 2; }
    q = atoi(argv[1]); n = atoi(argv[2]);
    double secs = atof(argv[3]);
    rng = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 0xD1B54A32D192ED03ULL;
    int K = atoi(argv[5]);
    if (q > MAXQ || n > MAXN || n < 4 || !field(q)) { fprintf(stderr, "q must be a supported prime power <= %d, 4 <= n <= %d\n", MAXQ, MAXN); return 2; }
    if (K < 6 || K > 65536) { fprintf(stderr, "need 6 <= K <= 65536\n"); return 2; }
    geometry();
    build_fields();
    int type2 = 0;  /* type-2 rows of order at least K exist? */
    { struct row R = {2, 1, 1}; type2 = rorder(&R) >= K; }
    double pbad = 1 - (1 - pow(q, -4)) * (1 - pow(q, -3)) * (1 - pow(q, -2)) * (1 - pow(q, -1));
    double sets = (double)(K - 1) * (K - 2) * (K - 3) * (K - 4) / 24;
    int C = argc > 6 ? atoi(argv[6]) : (int)ceil(log(sets / 1000) / -log(pbad));  /* about 1,000 sets left by chance */
    if (C < 1 || C > n - 2) { fprintf(stderr, "need 1 <= C <= n - 2 (C %d)\n", C); return 2; }
    uint32_t *A[MAXN];  /* the whole array, rows of K points */
    for (int r = 0; r < n; r++) { A[r] = malloc(sizeof(uint32_t) * K); H[r] = malloc(sizeof(uint32_t) * K); }
    nthreads = getenv("CPHF_THREADS") ? atoi(getenv("CPHF_THREADS")) : 6;
    if (nthreads < 1) nthreads = 1;
    if (nthreads > 64) nthreads = 64;
    CX = calloc(nthreads, sizeof(struct ctx));
    for (int w = 0; w < nthreads; w++) {
        struct ctx *X = &CX[w];
        for (int r = 0; r < n; r++) {
            X->cls[r] = malloc(sizeof(int) * K);
            X->CNT[r] = calloc(NN, sizeof(int)); X->OFF[r] = malloc(sizeof(int) * NN); X->TCH[r] = malloc(sizeof(int) * NN);
        }
        X->d0 = malloc(sizeof(int) * K); X->d1 = malloc(sizeof(int) * K); X->d2 = malloc(sizeof(int) * K); X->d3 = malloc(sizeof(int) * K);
    }
    int *L = malloc(sizeof(int) * K);
    THR = getenv("CPHF_THR") ? atoi(getenv("CPHF_THR")) : (int)(1.3 * cbrt(24.0 * NP));
    fprintf(stderr, "GF(%d^4) mod x^4 + %d x^3 + %d x^2 + %d x + %d, GF(%d^3) mod x^3 + %d x^2 + %d x + %d; type 2 %s; "
            "%.3g sets hold column 0; %d cyclic rows (about %.3g left by chance), %d random\n",
            q, f4c[3], f4c[2], f4c[1], f4c[0], q, f3c[2], f3c[1], f3c[0], type2 ? "used" : "too short, type 1 only",
            sets, C, sets * pow(pbad, C), n - C);
    struct row rows[MAXN];
    long *ush = NULL, nu = 0, capu = 0;  /* shifted sets left uncovered: index into S and shift */
    T0 = clock();
    for (int att = 1; (double)(clock() - T0) / CLOCKS_PER_SEC < secs; att++) {
        nused = 0;
        G = C;
        for (int r = 0; r < C; r++) {
            rows[r] = pick(K, type2 && r % 2 ? 2 : 1);
            used[nused++] = rclass(&rows[r]);
            fillrow(r, &rows[r], K);
            for (int j = 0; j < K; j++) A[r][j] = point(&rows[r], j);
        }
        k = K - 1;
        for (int i = 0; i < k; i++) L[i] = i;
        enumerate(L, k);
        double shifts = 0;
        for (long i = 0; i < nS; i++) shifts += K - 1 - (double)(S[i] & 0xFFFF) - 1;
        fprintf(stderr, "attempt %d: %ld sets holding column 0 fail in all %d cyclic rows, %.4g shifted sets, %.0f s\n",
                att, nS, C, shifts, (double)(clock() - T0) / CLOCKS_PER_SEC);
        int ok = 0;
        for (int tries = 0; tries < 50 && !ok && (double)(clock() - T0) / CLOCKS_PER_SEC < secs; tries++) {
            for (int r = C; r < n - 1; r++) for (int j = 0; j < K; j++) A[r][j] = (uint32_t)(rnd() % P);  /* same B */
            nu = 0;
            for (long i = 0; i < nS; i++) {
                long top = (long)(S[i] & 0xFFFF) + 1;
                for (long s0 = 0; s0 + top < K; s0++)
                    if (!covered(A + C, n - 1 - C, s0, S[i])) {
                        if (2 * nu + 2 > capu) { capu = capu ? capu * 2 : 1 << 16; ush = realloc(ush, sizeof(long) * capu); }
                        ush[2 * nu] = i; ush[2 * nu + 1] = s0; nu++;
                    }
            }
            fprintf(stderr, "  %ld shifted sets left after %d random rows, %.0f s\n", nu, n - 1 - C, (double)(clock() - T0) / CLOCKS_PER_SEC);
            for (int tr = 0; tr < 2000 && !ok; tr++) {  /* the last row: random until it covers all of them */
                for (int j = 0; j < K; j++) A[n - 1][j] = (uint32_t)(rnd() % P);
                ok = 1;
                for (long u = 0; u < nu && ok; u++) ok = covered(A + n - 1, 1, ush[2 * u + 1], S[ush[2 * u]]);
            }
            if (!ok) fprintf(stderr, "  no last row covers them\n");
        }
        if (!ok) continue;
        printf("best k %d (q %d, n %d, t 5, cyclic %d, %.0f s)\n", K, q, n, C, (double)(clock() - T0) / CLOCKS_PER_SEC);
        printf("# GF(%d^4) mod x^4 + %d x^3 + %d x^2 + %d x + %d, GF(%d^3) mod x^3 + %d x^2 + %d x + %d; cyclic rows (type, step):",
               q, f4c[3], f4c[2], f4c[1], f4c[0], q, f3c[2], f3c[1], f3c[0]);
        for (int r = 0; r < C; r++) printf(" (%d, %u%s%d)", rows[r].type, rows[r].type == 1 ? ex[rows[r].e] : ex3[rows[r].e],
                                           rows[r].type == 1 ? "" : " + ", rows[r].type == 1 ? 0 : rows[r].c);
        printf("; rows %d..%d random\n", C, n - 1);
        for (int r = 0; r < n; r++) {
            for (int j = 0; j < K; j++) printf(j ? " %u" : "%u", A[r][j]);
            printf("\n");
        }
        return 0;
    }
    printf("best k 0 (q %d, n %d, t 5, cyclic %d, %.0f s)\n", q, n, C, (double)(clock() - T0) / CLOCKS_PER_SEC);
    return 1;
}
