/* Strength-5 Sherwood CPHFs: SCPHF(n; k, q^4, 5), an n x k array of points of AG(4,q) in which any five columns
   hold, in some row, five points not on one hyperplane; by Sherwood, Martirosyan and Colbourn (2006) it gives
   CA(n(q^5 - q) + q; 5, k, q). Grown column by column as in cphf4m.c, one dimension up: in row r, old columns
   A, B, C, D and the new point p lie on one hyperplane exactly when the directions A - p, ..., D - p (points of
   PG(3,q)) lie on one plane; a column standing at p is on every plane. So the old columns are bucketed by every
   plane through their direction in row 0, each bucket again in row 1, and so on: the quadruples sharing a bucket
   are exactly those on one hyperplane with the new column in the rows bucketed so far. A bucket of at most THR
   columns is not split; its quadruples are listed (one dot product each, against a normal computed once per
   triple) and filtered through the remaining random rows. Rows 0..g-1 get random points (g leaves about 200,000
   quadruples, or about q when rows are to spare); rows g..n-2 are chosen greedily, each the point (all q^4, or 4096
   sampled, 1024 when every hyperplane normal must be scored) on the fewest remaining
   quadruples' hyperplanes; the last row takes a point on none of them (points tried in random order, at most
   LASTMAX). A failed candidate is redrawn; after TRIES failures in a row, 1-3 random columns are dropped (the best
   array is kept).
   Prints "best k K (q Q, n N, t 5, S s)", then the array (n lines of point ids ((x q + y) q + z) q + w).
   cc -O3 -o cphf5m cphf5m.c && ./cphf5m q n seconds seed [maxk] [tries]
   CPHF_START=FILE continues from an earlier result (its header line, then n rows of point ids); CPHF_THR sets THR. */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 25
#define MAXN 40
#define ALL 0xFFFFFFFFu
#define SMAX 200000.0  /* quadruples worth keeping for the greedy rows */
#define LASTMAX 50000  /* points tried for the last row */

static int q, P, n, NN, NP, NPL;
static int add[MAXQ][MAXQ], mul[MAXQ][MAXQ], sub[MAXQ][MAXQ], inv[MAXQ];
static uint8_t *px, *py, *pz, *pw;
static uint8_t (*nv)[4];           /* the NN points of PG(3,q), first nonzero coordinate 1; also the planes' normals */
static int *dcls;                  /* direction class of each difference vector (as a point id), -1 for zero */
static int *ptpl;                  /* the NP = q^2 + q + 1 planes of PG(3,q) through each point, NP per point */
static uint32_t *H[MAXN], *best[MAXN];
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

static inline int dot(int i, uint32_t p) {
    return add[add[mul[nv[i][0]][px[p]]][mul[nv[i][1]][py[p]]]][add[mul[nv[i][2]][pz[p]]][mul[nv[i][3]][pw[p]]]];
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

static uint32_t hyp4(uint32_t A, uint32_t B, uint32_t C, uint32_t D) {  /* hyperplane id through four points, ALL if
                                                                           they lie on a plane */
    int a0 = px[A], a1 = py[A], a2 = pz[A], a3 = pw[A], N0, N1, N2, N3;
    SPAN_NORMAL(sub[px[B]][a0], sub[py[B]][a1], sub[pz[B]][a2], sub[pw[B]][a3],
                sub[px[C]][a0], sub[py[C]][a1], sub[pz[C]][a2], sub[pw[C]][a3],
                sub[px[D]][a0], sub[py[D]][a1], sub[pz[D]][a2], sub[pw[D]][a3], N0, N1, N2, N3);
    if (!N0 && !N1 && !N2 && !N3) return ALL;
    int i = dirclass(N0, N1, N2, N3);
    return (uint32_t)(i * q + dot(i, A));
}

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

static int k, G, THR;              /* columns; rows with random points; bucket size listed directly */
static uint32_t cand[MAXN];
static int *ent[MAXN], *cls[MAXN], *CNT[MAXN], *OFF[MAXN], *TCH[MAXN];
static long entcap[MAXN];
static uint64_t *S; static long nS, capS;
static uint32_t *spl;              /* hyperplane of each kept quadruple in the row being chosen */

static void keep(int a, int b, int c, int d) {
    if (nS == capS) { capS = capS ? capS * 2 : 1 << 16; S = realloc(S, sizeof(uint64_t) * capS); spl = realloc(spl, sizeof(uint32_t) * capS); }
    S[nS++] = (uint64_t)a << 48 | (uint64_t)b << 32 | (uint64_t)c << 16 | (uint64_t)d;
}

static int *d0, *d1, *d2, *d3;     /* leaf scratch: differences from the first column of a quadruple */

static void leaf(const int *L, int len, int r0) {  /* quadruples of L (on one hyperplane with the new column in rows
                                                       0..r0-1), filtered through rows r0..G-1 */
    if (r0 >= G) {
        for (int x = 0; x < len; x++) for (int y = x + 1; y < len; y++) for (int z = y + 1; z < len; z++)
            for (int t = z + 1; t < len; t++) keep(L[x], L[y], L[z], L[t]);
        return;
    }
    const uint32_t *R = H[r0];
    uint32_t p = cand[r0];
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
                    if (ok) keep(a, b, c, d);
                }
            }
        }
    }
}

static void bucket(int lev, const int *L, int len) {  /* L ascending; every bucket keeps the order */
    if (lev == G || len <= THR) { leaf(L, len, lev); return; }
    uint32_t p = cand[lev];
    int *cnt = CNT[lev], *off = OFF[lev], *tch = TCH[lev], *cl = cls[lev], nt = 0;
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
    if (total > entcap[lev]) { entcap[lev] = total; ent[lev] = realloc(ent[lev], sizeof(int) * total); }
    int *e = ent[lev], s = 0;
    for (int t = 0; t < nt; t++) { off[tch[t]] = s; s += cnt[tch[t]]; }
    for (int x = 0; x < len; x++) {
        int d = cl[x];
        if (d < 0) for (int l = 0; l < NN; l++) e[off[l]++] = L[x];
        else { const int *pl = ptpl + (size_t)d * NP; for (int j = 0; j < NP; j++) e[off[pl[j]]++] = L[x]; }
    }
    for (int t = 0; t < nt; t++) {
        int l = tch[t], c = cnt[l];
        if (c >= 4) bucket(lev + 1, e + off[l] - c, c);
    }
    for (int t = 0; t < nt; t++) cnt[tch[t]] = 0;
}

static int *pcnt, *hl, nh;         /* count of kept quadruples on each hyperplane; the hyperplanes in use */
static long nall;                  /* kept quadruples whose four points lie on a plane (every point is bad) */

static void tally(int r) {
    nh = 0; nall = 0;
    for (long i = 0; i < nS; i++) {
        uint64_t t = S[i];
        uint32_t h = hyp4(H[r][t >> 48], H[r][t >> 32 & 0xFFFF], H[r][t >> 16 & 0xFFFF], H[r][t & 0xFFFF]);
        spl[i] = h;
        if (h == ALL) nall++;
        else if (pcnt[h]++ == 0) hl[nh++] = (int)h;
    }
}

static inline long score(uint32_t x, long cap) {  /* kept quadruples whose hyperplane holds x (stops past cap) */
    long c = 0;
    if (nh < NN) { for (int j = 0; j < nh && c <= cap; j++) { int h = hl[j]; if (dot(h / q, x) == h % q) c += pcnt[h]; } return c; }
    /* every normal: (1, b, c, d) first, then (0, 1, c, d), (0, 0, 1, d), (0, 0, 0, 1); dot products by partial sums */
    int x0 = px[x], t1[MAXQ], t2[MAXQ], t3[MAXQ];
    for (int v = 0; v < q; v++) { t1[v] = mul[v][py[x]]; t2[v] = mul[v][pz[x]]; t3[v] = mul[v][pw[x]]; }
    const int *pc = pcnt;
    for (int b = 0; b < q && c <= cap; b++) {
        int sb = add[x0][t1[b]];
        for (int cc = 0; cc < q; cc++, pc += q * q) {
            int sbc = add[sb][t2[cc]];
            for (int d = 0; d < q; d++) c += pc[d * q + add[sbc][t3[d]]];
        }
    }
    if (c > cap) return c;
    int y0 = py[x];
    for (int cc = 0; cc < q; cc++, pc += q * q) {
        int sc = add[y0][t2[cc]];
        for (int d = 0; d < q; d++) c += pc[d * q + add[sc][t3[d]]];
    }
    int z0 = pz[x];
    for (int d = 0; d < q; d++) c += pc[d * q + add[z0][t3[d]]];
    pc += q * q;
    c += pc[pw[x]];
    return c;
}

static void greedy(int r) {  /* row r's point: the one (of all q^4, or 4096 sampled) on the fewest kept hyperplanes */
    static uint32_t *samp;
    if (!samp) samp = malloc(sizeof(uint32_t) * 4096);
    tally(r);
    int ns = P <= 4096 ? P : nh < NN ? 4096 : NN <= 4096 ? 4096 : 1024, nb = 0;  /* fewer samples when every
                                                                                  normal is scored (q >= 16) */
    long bestc = -1;
    for (int i = 0; i < ns; i++) {
        uint32_t x = P <= 4096 ? (uint32_t)i : (uint32_t)(rnd() % P);
        long c = score(x, bestc < 0 ? (long)nS : bestc);
        if (bestc < 0 || c < bestc) { bestc = c; nb = 0; }
        if (c == bestc) samp[nb++] = x;
    }
    uint32_t x = samp[rnd() % nb];
    for (int j = 0; j < nh; j++) pcnt[hl[j]] = 0;
    cand[r] = x;
    long w = 0;  /* keep the quadruples whose hyperplane holds x (all where the four points lie on a plane) */
    for (long i = 0; i < nS; i++) {
        uint32_t h = spl[i];
        if (h == ALL || dot((int)(h / q), x) == (int)(h % q)) S[w++] = S[i];
    }
    nS = w;
}

static int lastrow(int r) {  /* a point on no kept quadruple's hyperplane in row r; 0 if none is found */
    tally(r);
    int ok = 0;
    if (!nall) {
        uint32_t x = (uint32_t)(rnd() % P), stride = 7919;  /* prime above 25: steps through every point */
        int tries = P < LASTMAX ? P : LASTMAX;
        for (int i = 0; i < tries; i++, x = (x + stride) % (uint32_t)P)
            if (score(x, 0) == 0) { cand[r] = x; ok = 1; break; }
    }
    for (int j = 0; j < nh; j++) pcnt[hl[j]] = 0;
    return ok;
}

static void depths(void) {  /* G: random rows, enough that about SMAX quadruples are left for the greedy rows; with
                               rows to spare, more random rows (cheap) until about q are left for one greedy row */
    double left = (double)k * (k - 1) * (k - 2) * (k - 3) / 24;
    G = 0;
    while (G < n - 1 && left > SMAX) { G++; left /= q; }
    while (G < n - 2 && left > q) { G++; left /= q; }
}

static int tryadd(int *L) {
    depths();
    for (int r = 0; r < G; r++) cand[r] = (uint32_t)(rnd() % P);
    nS = 0;
    bucket(0, L, k);
    for (int r = G; r < n - 1; r++) greedy(r);
    return lastrow(n - 1);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: cphf5m q n seconds seed [maxk] [tries]\n"); return 2; }
    q = atoi(argv[1]); n = atoi(argv[2]);
    double secs = atof(argv[3]);
    rng = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 0xD1B54A32D192ED03ULL;
    int maxk = argc > 5 ? atoi(argv[5]) : 3000;
    int tries = argc > 6 ? atoi(argv[6]) : 30;
    if (q > MAXQ || n > MAXN || n < 3 || !field(q)) { fprintf(stderr, "q must be a supported prime power <= %d, 3 <= n <= %d\n", MAXQ, MAXN); return 2; }
    if (maxk > 65535) maxk = 65535;
    geometry();
    for (int r = 0; r < n; r++) {
        H[r] = malloc(sizeof(uint32_t) * (maxk + 1)); best[r] = malloc(sizeof(uint32_t) * (maxk + 1));
        cls[r] = malloc(sizeof(int) * (maxk + 1));
        CNT[r] = calloc(NN, sizeof(int)); OFF[r] = malloc(sizeof(int) * NN); TCH[r] = malloc(sizeof(int) * NN);
    }
    pcnt = calloc(NPL, sizeof(int)); hl = malloc(sizeof(int) * NPL);
    int *L = malloc(sizeof(int) * (maxk + 1));
    d0 = malloc(sizeof(int) * (maxk + 1)); d1 = malloc(sizeof(int) * (maxk + 1));
    d2 = malloc(sizeof(int) * (maxk + 1)); d3 = malloc(sizeof(int) * (maxk + 1));
    THR = getenv("CPHF_THR") ? atoi(getenv("CPHF_THR")) : (int)(1.3 * cbrt(24.0 * NP));
    int bestk = 0;
    clock_t t0 = clock();
    k = 0;
    const char *sf = getenv("CPHF_START");
    if (sf) {
        FILE *f = fopen(sf, "r");
        if (!f || fscanf(f, "best k %d", &k) != 1 || k < 0 || k > maxk) { fprintf(stderr, "bad CPHF_START file\n"); return 2; }
        if (fscanf(f, "%*[^\n]") < 0) { fprintf(stderr, "bad CPHF_START file\n"); return 2; }
        for (int r = 0; r < n; r++)
            for (int c = 0; c < k; c++) {
                unsigned v;
                if (fscanf(f, "%u", &v) != 1 || v >= (unsigned)P) { fprintf(stderr, "bad CPHF_START file\n"); return 2; }
                H[r][c] = v;
            }
        fclose(f);
        bestk = k;
        for (int r = 0; r < n; r++) memcpy(best[r], H[r], sizeof(uint32_t) * k);
    }
    int fails = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && bestk < maxk) {
        for (int c = 0; c < k; c++) L[c] = c;
        if (tryadd(L)) {
            for (int r = 0; r < n; r++) H[r][k] = cand[r];
            k++;
            fails = 0;
            if (k > bestk) {
                bestk = k;
                for (int r = 0; r < n; r++) memcpy(best[r], H[r], sizeof(uint32_t) * k);
                if (bestk % 100 == 0) fprintf(stderr, "k %d at %.0f s (G %d)\n", bestk, (double)(clock() - t0) / CLOCKS_PER_SEC, G);
            }
        } else if (++fails >= tries) {
            int drop = 1 + (int)(rnd() % 3);
            for (int d = 0; d < drop && k > 0; d++) {
                int c = (int)(rnd() % k);
                k--;
                for (int r = 0; r < n; r++) H[r][c] = H[r][k];
            }
            fails = 0;
        }
    }
    printf("best k %d (q %d, n %d, t 5, %.0f s)\n", bestk, q, n, (double)(clock() - t0) / CLOCKS_PER_SEC);
    for (int r = 0; r < n; r++) {
        for (int c = 0; c < bestk; c++) printf(c ? " %u" : "%u", best[r][c]);
        printf("\n");
    }
    return 0;
}
