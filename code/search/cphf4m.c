/* Strength-4 Sherwood CPHFs with many columns (thousands to 10,000): SCPHF(n; k, q^3, 4) as in cphf4x.c, grown
   column by column, but a new column's conflicts are found without streaming every triple on a plane through its
   first-row point. In row r, old columns A, B, C and the new point p lie on one plane exactly when the directions
   A - p, B - p, C - p (points of PG(2,q)) lie on one line; a column standing at p is on every line. So the old
   columns are bucketed by every line through their direction in row 0, each bucket again in row 1, and so on: the
   triples sharing a bucket are exactly those on one plane with the new column in the rows bucketed so far. A
   bucket of at most q + 6 columns is not split further; its triples are listed, one dot product each, and
   filtered through the remaining random rows. Rows 0..g-1 get random points (g leaves about 200,000 triples);
   rows g..n-2 are chosen
   greedily, each the point (all q^3, or 4096 sampled) on the fewest remaining triples' planes; the last row takes a
   random point off the union of the remaining planes. A failed candidate is redrawn; after TRIES failures in a row, 1-3 random
   columns are dropped (the best array is kept).
   Prints "best k K (q Q, n N, t 4, S s)", then the array (n lines of point ids (x q + y) q + z), like cphf4x.
   cc -O3 -o cphf4m cphf4m.c && ./cphf4m q n seconds seed [maxk] [tries]
   CPHF_START=FILE continues from an earlier result (its header line, then n rows of point ids). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 25
#define MAXN 24
#define ALL 0xFFFFFFFFu
#define SMAX 200000.0  /* triples worth keeping for the greedy rows */

static int q, P, n, NN, NPL, Wq;
static int add[MAXQ][MAXQ], mul[MAXQ][MAXQ], sub[MAXQ][MAXQ], inv[MAXQ];
static uint8_t *px, *py, *pz;
static int nv[MAXQ * MAXQ + MAXQ + 1][3];
static uint64_t *pmask;
static int *dcls;                  /* direction class of each difference vector (dx q + dy) q + dz, -1 for zero */
static int (*ptlines)[MAXQ + 1];   /* the q + 1 lines of PG(2,q) through each point */
static uint16_t *H[MAXN], *best[MAXN];
static uint64_t rng;

static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static int field(int qq) {  /* GF(q) as in cphf4x.c */
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

static int dirclass(int a, int b, int c) {  /* class of a nonzero vector: first nonzero coordinate 1 */
    if (a) { int s = inv[a]; return mul[b][s] * q + mul[c][s]; }
    if (b) return q * q + mul[c][inv[b]];
    return q * q + q;
}

static int dot(int i, int p) { return add[add[mul[nv[i][0]][px[p]]][mul[nv[i][1]][py[p]]]][mul[nv[i][2]][pz[p]]]; }

static uint32_t plane3(int a, int b, int c) {  /* plane id through three points, ALL if they are collinear */
    int u1 = sub[px[b]][px[a]], u2 = sub[py[b]][py[a]], u3 = sub[pz[b]][pz[a]];
    int v1 = sub[px[c]][px[a]], v2 = sub[py[c]][py[a]], v3 = sub[pz[c]][pz[a]];
    int n1 = sub[mul[u2][v3]][mul[u3][v2]], n2 = sub[mul[u3][v1]][mul[u1][v3]], n3 = sub[mul[u1][v2]][mul[u2][v1]];
    if (!n1 && !n2 && !n3) return ALL;
    int i = dirclass(n1, n2, n3);
    return (uint32_t)(i * q + dot(i, a));
}

static int coplanar(int A, int B, int C, int p) {  /* det(B - A, C - A, p - A) == 0 */
    int u1 = sub[px[B]][px[A]], u2 = sub[py[B]][py[A]], u3 = sub[pz[B]][pz[A]];
    int v1 = sub[px[C]][px[A]], v2 = sub[py[C]][py[A]], v3 = sub[pz[C]][pz[A]];
    int w1 = sub[px[p]][px[A]], w2 = sub[py[p]][py[A]], w3 = sub[pz[p]][pz[A]];
    int c1 = sub[mul[v2][w3]][mul[v3][w2]], c2 = sub[mul[v3][w1]][mul[v1][w3]], c3 = sub[mul[v1][w2]][mul[v2][w1]];
    return add[add[mul[u1][c1]][mul[u2][c2]]][mul[u3][c3]] == 0;
}

static void geometry(void) {
    P = q * q * q; NN = q * q + q + 1; NPL = NN * q; Wq = (P + 63) / 64;
    px = malloc(P); py = malloc(P); pz = malloc(P);
    for (int p = 0; p < P; p++) { px[p] = (uint8_t)(p / (q * q)); py[p] = (uint8_t)(p / q % q); pz[p] = (uint8_t)(p % q); }
    for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) { nv[b * q + c][0] = 1; nv[b * q + c][1] = b; nv[b * q + c][2] = c; }
    for (int c = 0; c < q; c++) { nv[q * q + c][0] = 0; nv[q * q + c][1] = 1; nv[q * q + c][2] = c; }
    nv[q * q + q][0] = 0; nv[q * q + q][1] = 0; nv[q * q + q][2] = 1;
    pmask = calloc((size_t)NPL * Wq, sizeof(uint64_t));
    for (int i = 0; i < NN; i++)
        for (int p = 0; p < P; p++) { size_t id = (size_t)i * q + dot(i, p); pmask[id * Wq + (p >> 6)] |= 1ULL << (p & 63); }
    dcls = malloc(sizeof(int) * P);
    for (int v = 0; v < P; v++) dcls[v] = v ? dirclass(v / (q * q), v / q % q, v % q) : -1;
    ptlines = malloc(sizeof *ptlines * NN);
    for (int d = 0; d < NN; d++) {  /* line l holds point d when nv[l] . nv[d] = 0 */
        int j = 0;
        for (int l = 0; l < NN; l++) {
            int s = add[add[mul[nv[l][0]][nv[d][0]]][mul[nv[l][1]][nv[d][1]]]][mul[nv[l][2]][nv[d][2]]];
            if (!s) ptlines[d][j++] = l;
        }
        if (j != q + 1) { fprintf(stderr, "PG(2,q) incidence is wrong\n"); exit(3); }
    }
}

static int k, G, THR;              /* columns; rows with random points; bucket size listed directly */
static int cand[MAXN];
static int *ent[MAXN], *cls[MAXN], entcap[MAXN];
static uint64_t *S; static long nS, capS;
static uint32_t *spl;              /* plane of each kept triple in the row being chosen */

static void keep(int a, int b, int c) {
    if (nS == capS) { capS = capS ? capS * 2 : 1 << 16; S = realloc(S, sizeof(uint64_t) * capS); spl = realloc(spl, sizeof(uint32_t) * capS); }
    S[nS++] = (uint64_t)a << 32 | (uint64_t)b << 16 | (uint64_t)c;
}

static int *dX, *dY, *dZ;          /* leaf scratch: differences from the first column of a pair */

static void leaf(const int *L, int len, int r0) {  /* triples of L (on one plane with the new column in rows
                                                       0..r0-1), filtered through rows r0..G-1 */
    if (r0 >= G) {
        for (int x = 0; x < len; x++) for (int y = x + 1; y < len; y++) for (int z = y + 1; z < len; z++) keep(L[x], L[y], L[z]);
        return;
    }
    const uint16_t *R = H[r0];
    int p = cand[r0];
    for (int x = 0; x < len; x++) {
        int a = L[x], A = R[a], ax = px[A], ay = py[A], az = pz[A];
        int w1 = sub[px[p]][ax], w2 = sub[py[p]][ay], w3 = sub[pz[p]][az];
        for (int z = x + 1; z < len; z++) { int C = R[L[z]]; dX[z] = sub[px[C]][ax]; dY[z] = sub[py[C]][ay]; dZ[z] = sub[pz[C]][az]; }
        for (int y = x + 1; y < len; y++) {
            int b = L[y], u1 = dX[y], u2 = dY[y], u3 = dZ[y];
            int c1 = sub[mul[w2][u3]][mul[w3][u2]], c2 = sub[mul[w3][u1]][mul[w1][u3]], c3 = sub[mul[w1][u2]][mul[w2][u1]];
            for (int z = y + 1; z < len; z++) {  /* det(B - A, C - A, p - A) = (C - A) . ((p - A) x (B - A)) */
                if (add[add[mul[dX[z]][c1]][mul[dY[z]][c2]]][mul[dZ[z]][c3]]) continue;
                int c = L[z], ok = 1;
                for (int r = r0 + 1; r < G && ok; r++) ok = coplanar(H[r][a], H[r][b], H[r][c], cand[r]);
                if (ok) keep(a, b, c);
            }
        }
    }
}

static void bucket(int lev, const int *L, int len) {  /* L ascending; every bucket keeps the order */
    if (lev == G || len <= THR) { leaf(L, len, lev); return; }
    int p = cand[lev], cnt[MAXQ * MAXQ + MAXQ + 1], off[MAXQ * MAXQ + MAXQ + 1], *cl = cls[lev], total = 0;
    memset(cnt, 0, sizeof(int) * NN);
    for (int x = 0; x < len; x++) {
        int A = H[lev][L[x]];
        int d = dcls[(sub[px[A]][px[p]] * q + sub[py[A]][py[p]]) * q + sub[pz[A]][pz[p]]];
        cl[x] = d;
        if (d < 0) { for (int l = 0; l < NN; l++) cnt[l]++; total += NN; }
        else { for (int j = 0; j <= q; j++) cnt[ptlines[d][j]]++; total += q + 1; }
    }
    if (total > entcap[lev]) { entcap[lev] = total; ent[lev] = realloc(ent[lev], sizeof(int) * total); }
    int *e = ent[lev], s = 0;
    for (int l = 0; l < NN; l++) { off[l] = s; s += cnt[l]; }
    for (int x = 0; x < len; x++) {
        int d = cl[x];
        if (d < 0) for (int l = 0; l < NN; l++) e[off[l]++] = L[x];
        else for (int j = 0; j <= q; j++) e[off[ptlines[d][j]]++] = L[x];
    }
    for (int l = 0; l < NN; l++) if (cnt[l] >= 3) bucket(lev + 1, e + off[l] - cnt[l], cnt[l]);
}

static void greedy(int r) {  /* row r's point: the one (of all q^3, or 4096 sampled) on the fewest kept planes */
    static int *pcnt, *samp;
    if (!pcnt) { pcnt = calloc(NPL, sizeof(int)); samp = malloc(sizeof(int) * P); }
    for (long i = 0; i < nS; i++) {
        uint64_t t = S[i];
        uint32_t pl = plane3(H[r][t >> 32], H[r][t >> 16 & 0xFFFF], H[r][t & 0xFFFF]);
        spl[i] = pl;
        if (pl != ALL) pcnt[pl]++;
    }
    int ns = P <= 4096 ? P : 4096, bestc = -1, nb = 0;
    for (int i = 0; i < ns; i++) {
        int x = P <= 4096 ? i : (int)(rnd() % P), c = 0;
        for (int j = 0; j < NN && (bestc < 0 || c <= bestc); j++) c += pcnt[j * q + dot(j, x)];
        if (bestc < 0 || c < bestc) { bestc = c; nb = 0; }
        if (c == bestc) samp[nb++] = x;
    }
    int x = samp[rnd() % nb];
    for (long i = 0; i < nS; i++) if (spl[i] != ALL) pcnt[spl[i]] = 0;
    cand[r] = x;
    long w = 0;  /* keep the triples whose plane holds x (all where the three points are collinear) */
    for (long i = 0; i < nS; i++) {
        uint32_t pl = spl[i];
        if (pl == ALL || dot((int)(pl / q), x) == (int)(pl % q)) S[w++] = S[i];
    }
    nS = w;
}

static int lastrow(int r) {  /* a random point off every kept triple's plane in row r; 0 if there is none */
    static uint64_t *u;
    if (!u) u = malloc(sizeof(uint64_t) * Wq);
    memset(u, 0, sizeof(uint64_t) * Wq);
    for (long i = 0; i < nS; i++) {
        uint64_t t = S[i];
        uint32_t pl = plane3(H[r][t >> 32], H[r][t >> 16 & 0xFFFF], H[r][t & 0xFFFF]);
        if (pl == ALL) return 0;
        const uint64_t *m = pmask + (size_t)pl * Wq;
        for (int w = 0; w < Wq; w++) u[w] |= m[w];
    }
    int nfree = 0;
    for (int p = 0; p < P; p++) nfree += !(u[p >> 6] >> (p & 63) & 1);
    if (!nfree) return 0;
    int j = (int)(rnd() % nfree);
    for (int p = 0; p < P; p++)
        if (!(u[p >> 6] >> (p & 63) & 1) && j-- == 0) { cand[r] = p; return 1; }
    return 0;
}

static void depths(void) {  /* G: random rows, enough that about SMAX triples are left for the greedy rows */
    double left = (double)k * k * k / 6;
    G = 0;
    while (G < n - 1 && left > SMAX) { G++; left /= q; }
}

static int tryadd(int *L) {
    depths();
    for (int r = 0; r < G; r++) cand[r] = (int)(rnd() % P);
    nS = 0;
    bucket(0, L, k);
    for (int r = G; r < n - 1; r++) greedy(r);
    return lastrow(n - 1);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: cphf4m q n seconds seed [maxk] [tries]\n"); return 2; }
    q = atoi(argv[1]); n = atoi(argv[2]);
    double secs = atof(argv[3]);
    rng = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 0xD1B54A32D192ED03ULL;
    int maxk = argc > 5 ? atoi(argv[5]) : 10000;
    int tries = argc > 6 ? atoi(argv[6]) : 30;
    if (q > MAXQ || n > MAXN || n < 3 || !field(q)) { fprintf(stderr, "q must be a supported prime power <= %d, 3 <= n <= %d\n", MAXQ, MAXN); return 2; }
    if (maxk > 65535) maxk = 65535;
    geometry();
    for (int r = 0; r < n; r++) {
        H[r] = malloc(sizeof(uint16_t) * (maxk + 1)); best[r] = malloc(sizeof(uint16_t) * (maxk + 1));
        cls[r] = malloc(sizeof(int) * (maxk + 1));
    }
    int *L = malloc(sizeof(int) * (maxk + 1));
    dX = malloc(sizeof(int) * (maxk + 1)); dY = malloc(sizeof(int) * (maxk + 1)); dZ = malloc(sizeof(int) * (maxk + 1));
    THR = q + 6;
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
                H[r][c] = (uint16_t)v;
            }
        fclose(f);
        bestk = k;
        for (int r = 0; r < n; r++) memcpy(best[r], H[r], sizeof(uint16_t) * k);
    }
    int fails = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && bestk < maxk) {
        for (int c = 0; c < k; c++) L[c] = c;
        if (tryadd(L)) {
            for (int r = 0; r < n; r++) H[r][k] = (uint16_t)cand[r];
            k++;
            fails = 0;
            if (k > bestk) {
                bestk = k;
                for (int r = 0; r < n; r++) memcpy(best[r], H[r], sizeof(uint16_t) * k);
                if (bestk % 500 == 0) fprintf(stderr, "k %d at %.0f s (G %d)\n", bestk, (double)(clock() - t0) / CLOCKS_PER_SEC, G);
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
    printf("best k %d (q %d, n %d, t 4, %.0f s)\n", bestk, q, n, (double)(clock() - t0) / CLOCKS_PER_SEC);
    for (int r = 0; r < n; r++) {
        for (int c = 0; c < bestk; c++) printf(c ? " %d" : "%d", best[r][c]);
        printf("\n");
    }
    return 0;
}
