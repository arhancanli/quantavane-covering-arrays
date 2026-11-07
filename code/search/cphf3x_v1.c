/* Sherwood covering perfect hash families of strength 3 with many columns (thousands to tens of thousands): the
   search of cphf3.c without storing every pair of old columns. A first-row point p0 spoils only the pairs whose two
   first-row points coincide, include p0, or lie on a line through p0: about k^2 / 2q pairs, listed from the columns
   standing on each line through p0. The later rows filter that list as in cphf3.c (depth first; the last row needs a
   point off the union of the remaining pairs' lines). When no column fits: least-conflict swap or random drops.
   Prints "best k K", then the array (n lines of k point ids x*q + y).
   cc -O3 -o cphf3x cphf3x.c && ./cphf3x q n seconds seed [maxk] [tries] [maxviol] */
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
#define MAXK 65535
#define ALL 0xFFFF

static int q, P, n, NL, Wq;
static int add[MAXQ][MAXQ], mul[MAXQ][MAXQ];
static uint16_t pairline[MAXP][MAXP];
static uint64_t linemask[MAXL][W];
static int ptson[MAXL][MAXQ];          /* the q points of each line */
static int linesat[MAXP][MAXQ + 1];    /* the q + 1 lines through each point */
static int nlinesat[MAXP];
static uint16_t *H[MAXN], *best[MAXN];
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
    memset(nlinesat, 0, sizeof nlinesat);
    for (int dir = 0; dir <= q; dir++)
        for (int off = 0; off < q; off++, NL++) {
            int dx = dir < q ? 1 : 0, dy = dir < q ? dir : 1;
            int ax = dir < q ? 0 : off, ay = dir < q ? off : 0;  /* lines y = s x + off, and x = off */
            int *pts = ptson[NL];
            memset(linemask[NL], 0, sizeof linemask[NL]);
            for (int t = 0; t < q; t++) {
                int x = add[ax][mul[t][dx]], y = add[ay][mul[t][dy]];
                pts[t] = x * q + y;
                linemask[NL][pts[t] >> 6] |= 1ULL << (pts[t] & 63);
                linesat[pts[t]][nlinesat[pts[t]]++] = NL;
            }
            for (int i = 0; i < q; i++) for (int j = 0; j < q; j++) if (i != j) pairline[pts[i]][pts[j]] = (uint16_t)NL;
        }
}

static int k;
static int *cstart, *clist;     /* first-row incidence: columns at point p are clist[cstart[p] .. cstart[p+1]) */
static uint32_t *stk, *stkend;  /* pair lists (a << 16 | b), one region per depth */
static uint32_t *A;             /* pairs whose first-row points coincide (spoiled by every p0) */
static long nA, capA;

static int lineid(int r, uint32_t pr) {
    int a = pr >> 16, b = pr & 0xFFFF;
    return H[r][a] == H[r][b] ? ALL : pairline[H[r][a]][H[r][b]];
}

static int on(int id, int p) { return id == ALL || (linemask[id][p >> 6] >> (p & 63) & 1); }

static void incidence(void) {  /* first-row incidence and the pairs that share a first-row point */
    memset(cstart, 0, sizeof(int) * (P + 1));
    for (int c = 0; c < k; c++) cstart[H[0][c] + 1]++;
    for (int p = 0; p < P; p++) cstart[p + 1] += cstart[p];
    static int fill[MAXP];
    memcpy(fill, cstart, sizeof(int) * P);
    for (int c = 0; c < k; c++) clist[fill[H[0][c]]++] = c;
    nA = 0;
    for (int p = 0; p < P; p++)
        for (int i = cstart[p]; i < cstart[p + 1]; i++)
            for (int j = i + 1; j < cstart[p + 1]; j++) {
                if (nA == capA) { capA = capA * 2 + 1024; A = realloc(A, sizeof(uint32_t) * capA); }
                A[nA++] = (uint32_t)clist[i] << 16 | (uint32_t)clist[j];
            }
}

static long spoiled(int p0, uint32_t *out) {  /* pairs spoiled in the first row by p0; -1 if out of room */
    long m = 0, room = stkend - out;
    if (nA > room) return -1;
    memcpy(out, A, sizeof(uint32_t) * nA);
    m = nA;
    for (int i = cstart[p0]; i < cstart[p0 + 1]; i++)  /* a column at p0 with any column elsewhere */
        for (int b = 0; b < k; b++) {
            if (H[0][b] == p0) continue;
            if (m == room) return -1;
            out[m++] = (uint32_t)clist[i] << 16 | (uint32_t)b;
        }
    for (int l = 0; l < nlinesat[p0]; l++) {  /* columns at two different points of a line through p0 */
        const int *pts = ptson[linesat[p0][l]];
        for (int s = 0; s < q; s++) {
            if (pts[s] == p0) continue;
            for (int u = s + 1; u < q; u++) {
                if (pts[u] == p0) continue;
                for (int i = cstart[pts[s]]; i < cstart[pts[s] + 1]; i++)
                    for (int j = cstart[pts[u]]; j < cstart[pts[u] + 1]; j++) {
                        if (m == room) return -1;
                        out[m++] = (uint32_t)clist[i] << 16 | (uint32_t)clist[j];
                    }
            }
        }
    }
    return m;
}

static int tries, maxviol;
static uint16_t cand[MAXN];
static long minviol;
static uint16_t mincand[MAXN];
static int cnt[MAXP];

static int dfs(int r, uint32_t *act, long na) {  /* act: pairs spoiled in every row before r */
    if (r == n - 1) {
        uint64_t u[W] = {0};
        for (long i = 0; i < na; i++) {
            int id = lineid(r, act[i]);
            if (id == ALL) return 0;
            for (int w = 0; w < Wq; w++) u[w] |= linemask[id][w];
        }
        int free = 0;
        for (int p = 0; p < P; p++) free += !(u[p >> 6] >> (p & 63) & 1);
        if (!free) {
            if (na <= minviol) {  /* least-conflict point: lies on the fewest of the remaining lines */
                memset(cnt, 0, sizeof(int) * P);
                for (long i = 0; i < na; i++) {
                    int id = lineid(r, act[i]);
                    for (int w = 0; w < Wq; w++)
                        for (uint64_t x = linemask[id][w]; x; x &= x - 1) cnt[w * 64 + __builtin_ctzll(x)]++;
                }
                int bp = -1, bc = (int)na + 1, ties = 0;
                for (int p = 0; p < P; p++)
                    if (cnt[p] < bc) { bc = cnt[p]; bp = p; ties = 1; }
                    else if (cnt[p] == bc && rnd() % ++ties == 0) bp = p;
                if (bc < minviol) { minviol = bc; memcpy(mincand, cand, sizeof cand); mincand[r] = (uint16_t)bp; }
            }
            return 0;
        }
        int pick = (int)(rnd() % (uint64_t)free);
        for (int p = 0; p < P; p++) if (!(u[p >> 6] >> (p & 63) & 1) && pick-- == 0) { cand[r] = (uint16_t)p; return 1; }
        return 0;
    }
    uint32_t *nxt = act + na;
    if (stkend - nxt < na) return 0;
    for (int t = 0; t < tries; t++) {
        int p = (int)(rnd() % (uint64_t)P);
        long m = 0;
        for (long i = 0; i < na; i++) if (on(lineid(r, act[i]), p)) nxt[m++] = act[i];
        cand[r] = (uint16_t)p;
        if (dfs(r + 1, nxt, m)) return 1;
    }
    return 0;
}

static int extend(void) {
    incidence();
    minviol = 1L << 40;
    for (int t = 0; t < tries; t++) {
        int p0 = (int)(rnd() % (uint64_t)P);
        long m = spoiled(p0, stk);
        if (m < 0) continue;
        cand[0] = (uint16_t)p0;
        if (dfs(1, stk, m)) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: cphf3x q n seconds seed [maxk] [tries] [maxviol]\n"); return 2; }
    q = atoi(argv[1]); n = atoi(argv[2]);
    double secs = atof(argv[3]);
    rng = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 0xD1B54A32D192ED03ULL;
    int maxk = argc > 5 ? atoi(argv[5]) : 4096;
    tries = argc > 6 ? atoi(argv[6]) : 4 * q;
    maxviol = argc > 7 ? atoi(argv[7]) : 3;
    if (q > MAXQ || n > MAXN || n < 2 || !field(q)) { fprintf(stderr, "q must be a supported prime power <= %d\n", MAXQ); return 2; }
    P = q * q; Wq = (P + 63) / 64;
    lines();
    if (maxk > MAXK) maxk = MAXK;
    for (int r = 0; r < n; r++) { H[r] = malloc(sizeof(uint16_t) * (maxk + 1)); best[r] = malloc(sizeof(uint16_t) * (maxk + 1)); }
    cstart = malloc(sizeof(int) * (P + 1)); clist = malloc(sizeof(int) * (maxk + 1));
    size_t cap = (size_t)maxk * maxk / q * 2 + (size_t)maxk * 8 + 4096;  /* about four times the first-row list */
    stk = malloc(sizeof(uint32_t) * cap); stkend = stk + cap;
    capA = 1024; A = malloc(sizeof(uint32_t) * capA);
    static int deg[MAXK + 1];
    static uint8_t gone[MAXK + 1];
    int bestk = 0;
    clock_t t0 = clock();
    k = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && bestk < maxk) {
        if (k < maxk && extend()) {
            for (int r = 0; r < n; r++) H[r][k] = cand[r];
            k++;
            if (k > bestk) { bestk = k; for (int r = 0; r < n; r++) memcpy(best[r], H[r], sizeof(uint16_t) * k); }
        } else if (minviol <= maxviol) {  /* add the least-conflict column, then drop columns to clear its conflicts */
            long m = spoiled(mincand[0], stk), nv = 0;
            if (m < 0) continue;
            for (long i = 0; i < m; i++) {
                int all = 1;
                for (int r = 1; r < n && all; r++) all = on(lineid(r, stk[i]), mincand[r]);
                if (all) stk[nv++] = stk[i];
            }
            memset(deg, 0, sizeof(int) * k); memset(gone, 0, (size_t)k);
            for (long j = 0; j < nv; j++) { deg[stk[j] >> 16]++; deg[stk[j] & 0xFFFF]++; }
            for (;;) {  /* greedy cover of the uncovered pairs by columns to remove */
                int bc = -1, bd = 0, ties = 0;
                for (int c = 0; c < k; c++)
                    if (!gone[c] && deg[c] > bd) { bd = deg[c]; bc = c; ties = 1; }
                    else if (!gone[c] && deg[c] == bd && bd > 0 && rnd() % ++ties == 0) bc = c;
                if (bd == 0) break;
                gone[bc] = 1;
                for (long j = 0; j < nv; j++) {
                    if (stk[j] == 0xFFFFFFFFu) continue;
                    int a = stk[j] >> 16, b = stk[j] & 0xFFFF;
                    if (a == bc || b == bc) { deg[a]--; deg[b]--; stk[j] = 0xFFFFFFFFu; }
                }
            }
            int m2 = 0;
            for (int c = 0; c < k; c++) if (!gone[c]) { for (int r = 0; r < n; r++) H[r][m2] = H[r][c]; m2++; }
            k = m2;
            for (int r = 0; r < n; r++) H[r][k] = mincand[r];
            k++;
            if (k > bestk) { bestk = k; for (int r = 0; r < n; r++) memcpy(best[r], H[r], sizeof(uint16_t) * k); }
        } else {
            int drop = 1 + (int)(rnd() % 3);
            for (int d = 0; d < drop && k > 0; d++) {
                int c = (int)(rnd() % (uint64_t)k);
                for (int r = 0; r < n; r++) H[r][c] = H[r][k - 1];
                k--;
            }
        }
    }
    printf("best k %d (q %d, n %d, %.0f s)\n", bestk, q, n, (double)(clock() - t0) / CLOCKS_PER_SEC);
    for (int r = 0; r < n; r++) {
        for (int c = 0; c < bestk; c++) printf(c ? " %d" : "%d", best[r][c]);
        printf("\n");
    }
    return 0;
}
