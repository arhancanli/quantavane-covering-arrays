/* Sherwood covering perfect hash families of strength 3: SCPHF(n; k, q^2, 3), an n x k array of points of the affine
   plane AG(2,q) in which any three columns hold, in some row, three distinct points not on one line. It gives a
   covering array CA(n(q^3 - q) + q; 3, k, q) (Sherwood, Martirosyan and Colbourn 2006): row u = (u0, u1, u2) of
   block r puts u0 + u1 x + u2 y in a column whose point in row r is (x, y).
   Search: grow the array one column at a time. A new column must, for every pair of old columns, avoid in some row
   the line through that pair's two points there (or any point, where the pair's points coincide). Depth first over
   the rows: each row's point keeps only the pairs whose line it lies on; the last row needs a point off the union of
   the remaining lines. When no column fits, take the column that leaves the fewest pairs uncovered (if at most maxviol),
   add it and remove a greedy cover of those pairs' columns; otherwise drop a few random columns. Keep the best array.
   Prints "best k K", then the array (n lines of k point ids x*q + y).
   cc -O3 -o cphf3 cphf3.c && ./cphf3 q n seconds seed [maxk] [tries] [maxviol] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 32
#define MAXP (MAXQ * MAXQ)
#define MAXL (MAXQ * MAXQ + MAXQ)
#define W ((MAXP + 63) / 64)
#define MAXN 12
#define MAXK 8192
#define ALL 0xFFFF

static int q, P, n, NL, Wq;  /* Wq: words of a point mask in use */
static int add[MAXQ][MAXQ], mul[MAXQ][MAXQ];
static uint16_t pairline[MAXP][MAXP];
static uint64_t linemask[MAXL][W];
static uint16_t H[MAXN][MAXK], best[MAXN][MAXK];
static uint64_t rng;

static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static int field(int qq) {  /* GF(q) tables, elements as base-p digit vectors, multiplication modulo a fixed
                               irreducible polynomial (coefficients low degree first, monic, degree m) */
    static const struct { int q, p, m, poly[6]; } F[] = {
        {4, 2, 2, {1, 1, 1}}, {8, 2, 3, {1, 1, 0, 1}}, {16, 2, 4, {1, 1, 0, 0, 1}}, {32, 2, 5, {1, 0, 1, 0, 0, 1}},
        {9, 3, 2, {1, 0, 1}}, {27, 3, 3, {1, 2, 0, 1}}, {25, 5, 2, {2, 1, 1}}};
    int p = 0, m = 0; const int *poly = NULL;
    for (int i = 0; i < 7; i++) if (F[i].q == qq) { p = F[i].p; m = F[i].m; poly = F[i].poly; }
    if (!p) {
        for (int d = 2; d * d <= qq; d++) if (qq % d == 0) return 0;
        for (int a = 0; a < qq; a++) for (int b = 0; b < qq; b++) { add[a][b] = (a + b) % qq; mul[a][b] = a * b % qq; }
        return 1;
    }
    for (int a = 0; a < qq; a++)
        for (int b = 0; b < qq; b++) {
            int da[8], db[8], s = 0, pw = 1, prod[16] = {0};
            for (int i = 0, x = a, y = b; i < m; i++, x /= p, y /= p) { da[i] = x % p; db[i] = y % p; }
            for (int i = 0; i < m; i++) { s += ((da[i] + db[i]) % p) * pw; pw *= p; }
            add[a][b] = s;
            for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) prod[i + j] = (prod[i + j] + da[i] * db[j]) % p;
            for (int d = 2 * m - 2; d >= m; d--)  /* reduce: x^m = -(poly[0] + ... + poly[m-1] x^(m-1)) */
                if (prod[d]) { int c = prod[d]; prod[d] = 0; for (int i = 0; i < m; i++) prod[d - m + i] = ((prod[d - m + i] - c * poly[i]) % p + p) % p; }
            s = 0; pw = 1;
            for (int i = 0; i < m; i++) { s += prod[i] * pw; pw *= p; }
            mul[a][b] = s;
        }
    return 1;
}

static void lines(void) {  /* every line {a + t d}: directions (1, s) and (0, 1); ids 0..q^2+q-1 */
    NL = 0;
    for (int dir = 0; dir <= q; dir++)
        for (int off = 0; off < q; off++, NL++) {
            int dx = dir < q ? 1 : 0, dy = dir < q ? dir : 1;
            int ax = dir < q ? 0 : off, ay = dir < q ? off : 0;  /* lines y = s x + off, and x = off */
            int pts[MAXQ];
            memset(linemask[NL], 0, sizeof linemask[NL]);
            for (int t = 0; t < q; t++) {
                int x = add[ax][mul[t][dx]], y = add[ay][mul[t][dy]];
                pts[t] = x * q + y;
                linemask[NL][pts[t] >> 6] |= 1ULL << (pts[t] & 63);
            }
            for (int i = 0; i < q; i++) for (int j = 0; j < q; j++) if (i != j) pairline[pts[i]][pts[j]] = (uint16_t)NL;
        }
}

static int k;                   /* columns in H */
static uint16_t *bad[MAXN];     /* bad[r][pair]: line id of the pair's two points in row r, or ALL */
static int npairs;
static uint16_t *pa, *pb;       /* the pair's two columns */

static void addpair(int a, int b) {
    pa[npairs] = (uint16_t)a; pb[npairs] = (uint16_t)b;
    for (int r = 0; r < n; r++) bad[r][npairs] = H[r][a] == H[r][b] ? ALL : pairline[H[r][a]][H[r][b]];
    npairs++;
}

static void pairs_build(void) {
    npairs = 0;
    for (int a = 0; a < k; a++)
        for (int b = a + 1; b < k; b++) addpair(a, b);
}

static int on(int id, int p) { return id == ALL || (linemask[id][p >> 6] >> (p & 63) & 1); }

static int tries, maxviol;      /* points tried per row before giving up on a branch; largest conflict swap */
static uint16_t cand[MAXN];
static int minviol;             /* fewest pairs a candidate column leaves uncovered, this attempt */
static uint16_t mincand[MAXN];
static int cnt[MAXP];

static int dfs(int r, int *act, int na, int *buf) {  /* act: pairs not yet covered by rows < r */
    if (r == n - 1) {
        uint64_t u[W] = {0};
        for (int i = 0; i < na; i++) {
            int id = bad[r][act[i]];
            if (id == ALL) return 0;
            for (int w = 0; w < Wq; w++) u[w] |= linemask[id][w];
        }
        int free = 0;
        for (int p = 0; p < P; p++) free += !(u[p >> 6] >> (p & 63) & 1);
        if (!free) {
            if (na <= minviol) {  /* least-conflict point: lies on the fewest of the remaining lines */
                memset(cnt, 0, sizeof(int) * P);
                for (int i = 0; i < na; i++) {
                    int id = bad[r][act[i]];
                    for (int w = 0; w < Wq; w++)
                        for (uint64_t x = linemask[id][w]; x; x &= x - 1) cnt[w * 64 + __builtin_ctzll(x)]++;
                }
                int bp = -1, bc = na + 1, ties = 0;
                for (int p = 0; p < P; p++)
                    if (cnt[p] < bc) { bc = cnt[p]; bp = p; ties = 1; }
                    else if (cnt[p] == bc && rnd() % ++ties == 0) bp = p;
                if (bc < minviol) { minviol = bc; memcpy(mincand, cand, sizeof cand); mincand[r] = (uint16_t)bp; }
            }
            return 0;
        }
        int pick = rnd() % free;
        for (int p = 0; p < P; p++) if (!(u[p >> 6] >> (p & 63) & 1) && pick-- == 0) { cand[r] = (uint16_t)p; return 1; }
        return 0;
    }
    int *nxt = buf + na;
    for (int t = 0; t < tries; t++) {
        int p = rnd() % P, m = 0;
        for (int i = 0; i < na; i++) if (on(bad[r][act[i]], p)) nxt[m++] = act[i];
        cand[r] = (uint16_t)p;
        if (dfs(r + 1, nxt, m, nxt)) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: cphf3 q n seconds seed [maxk] [tries]\n"); return 2; }
    q = atoi(argv[1]); n = atoi(argv[2]);
    double secs = atof(argv[3]);
    rng = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 0xD1B54A32D192ED03ULL;
    int maxk = argc > 5 ? atoi(argv[5]) : 1024;
    tries = argc > 6 ? atoi(argv[6]) : 4 * q;
    maxviol = argc > 7 ? atoi(argv[7]) : 3;
    if (q > MAXQ || n > MAXN || n < 2 || !field(q)) { fprintf(stderr, "q must be a supported prime power <= %d\n", MAXQ); return 2; }
    P = q * q; Wq = (P + 63) / 64;
    lines();
    if (maxk > MAXK) maxk = MAXK;
    size_t mp = (size_t)maxk * (maxk - 1) / 2 + 1;  /* pairs at most */
    for (int r = 0; r < n; r++) bad[r] = malloc(sizeof(uint16_t) * mp);
    int *act = malloc(sizeof(int) * mp), *buf = malloc(sizeof(int) * mp * (n + 1));
    pa = malloc(sizeof(uint16_t) * mp); pb = malloc(sizeof(uint16_t) * mp);
    int bestk = 0;
    clock_t t0 = clock();
    k = 0;
    int dirty = 1;  /* pairs need a full rebuild (after columns were removed) */
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && bestk < maxk) {
        if (dirty) { pairs_build(); dirty = 0; }
        for (int i = 0; i < npairs; i++) act[i] = i;
        minviol = 1 << 30;
        if (k < maxk && dfs(0, act, npairs, buf)) {
            for (int r = 0; r < n; r++) H[r][k] = cand[r];
            k++;
            for (int a = 0; a < k - 1; a++) addpair(a, k - 1);
            if (k > bestk) { bestk = k; for (int r = 0; r < n; r++) memcpy(best[r], H[r], sizeof(uint16_t) * k); }
        } else if (minviol <= maxviol) {  /* add the least-conflict column, then drop columns to clear its conflicts */
            static int deg[MAXK];
            static uint8_t gone[MAXK];
            memset(deg, 0, sizeof(int) * k); memset(gone, 0, (size_t)k);
            int nv = 0;
            for (int i = 0; i < npairs; i++) {
                int all = 1;
                for (int r = 0; r < n && all; r++) all = on(bad[r][i], mincand[r]);
                if (all) { act[nv++] = i; deg[pa[i]]++; deg[pb[i]]++; }
            }
            for (;;) {  /* greedy cover of the uncovered pairs by columns to remove */
                int bc = -1, bd = 0, ties = 0;
                for (int c = 0; c < k; c++)
                    if (!gone[c] && deg[c] > bd) { bd = deg[c]; bc = c; ties = 1; }
                    else if (!gone[c] && deg[c] == bd && bd > 0 && rnd() % ++ties == 0) bc = c;
                if (bd == 0) break;
                gone[bc] = 1;
                for (int j = 0; j < nv; j++) {
                    int i = act[j];
                    if (i >= 0 && (pa[i] == bc || pb[i] == bc)) { deg[pa[i]]--; deg[pb[i]]--; act[j] = -1; }
                }
            }
            int m = 0;
            for (int c = 0; c < k; c++) if (!gone[c]) { for (int r = 0; r < n; r++) H[r][m] = H[r][c]; m++; }
            k = m;
            for (int r = 0; r < n; r++) H[r][k] = mincand[r];
            k++;
            dirty = 1;
            if (k > bestk) { bestk = k; for (int r = 0; r < n; r++) memcpy(best[r], H[r], sizeof(uint16_t) * k); }
        } else {
            int drop = 1 + (int)(rnd() % 3);
            for (int d = 0; d < drop && k > 0; d++) {
                int c = (int)(rnd() % k);
                for (int r = 0; r < n; r++) H[r][c] = H[r][k - 1];
                k--;
            }
            dirty = 1;
        }
    }
    printf("best k %d (q %d, n %d, %.0f s)\n", bestk, q, n, (double)(clock() - t0) / CLOCKS_PER_SEC);
    for (int r = 0; r < n; r++) {
        for (int c = 0; c < bestk; c++) printf(c ? " %d" : "%d", best[r][c]);
        printf("\n");
    }
    return 0;
}
