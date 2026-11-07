/* pq_cphf3big: Sherwood covering perfect hash families of strength 3, SCPHF(n; k, q^2, 3), with up to a few hundred
   thousand columns and little memory (3 Nov 2026). It gives CA(n(q^3 - q) + q; 3, k, q) as cphf3.c explains.

   Old method (cphf3x): list every pair of old columns that a first-row point spoils, about k^2 / 2q pairs per try:
   gigabytes and seconds per column at k = 100,000. Here no pair of old columns is ever listed while it is common.
   Seen from the new column's point c_r in row r, every old column b has a direction: the line through c_r and its
   point (one of q + 1), or STAR when it stands on c_r. The triple (a, b, new) is spoiled in row r exactly when the
   directions of a and b agree or one is STAR. So the new column is valid iff no two old columns agree, STAR matching
   anything, in every row. The search keeps, row by row, the classes of old columns that agree on the rows chosen so
   far (STAR columns copied into every class of their group; classes of one column dropped): O(k) per row.
   Rows whose classes are still large get a random point. Once few pairs are left, every point of the row is scored
   at once (pairs left after it: sum over lines L through x of C(m_L, 2) - q C(m_x, 2) per class) and the best two
   are tried. The last two rows are solved exactly: for every point x of row n-2, the union of the lines (in row
   n-1) of the pairs x leaves; a point off that union completes a valid column.
   When no column fits after `tries` attempts: the least-conflict column seen (at most maxviol pairs left) is added
   and a greedy cover of its conflict pairs' columns is removed; otherwise one to three random columns are dropped.
   The best array is kept (copied only before a removal) and written to OUT (atomically) every 60 s of CPU time,
   when the run ends, on SIGTERM/SIGINT, or when it stalls (no new best for stall_seconds).
   Field and lines exactly as cphf3x.c (point id x*q + y, field elements as base-p digit vectors), so PQ_START can
   continue any cphf3x / cphf3 result: its header line, then n rows of point ids.

   cc -O3 -march=native -o pq_cphf3big pq_cphf3big.c
   pq_cphf3big q n maxk cpu_seconds seed OUT [stall_seconds] [maxviol] [tries] */
#include <math.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define MAXQ 32
#define MAXP (MAXQ * MAXQ)
#define MAXL (MAXQ * MAXQ + MAXQ)
#define MAXW ((MAXP + 63) / 64)
#define MAXN 24
#define MAXK 1000000

static int q, P, n, NL, W;
static int add_[MAXQ][MAXQ], mul_[MAXQ][MAXQ];
static uint16_t *pairline;  /* P*P: the line through two distinct points */
static uint8_t *dirtab;     /* P*P: dirtab[x*P + y] = direction (0..q) of y seen from x; q + 1 if y == x */
static int ptson[MAXL][MAXQ];
static int linesat[MAXP][MAXQ + 1];
static uint64_t linemask[MAXL][MAXW];
static uint64_t rng;

static inline uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int field(int qq) {  /* as cphf3x.c */
    static const struct { int q, p, m, poly[6]; } F[] = {
        {4, 2, 2, {1, 1, 1}}, {8, 2, 3, {1, 1, 0, 1}}, {16, 2, 4, {1, 1, 0, 0, 1}}, {32, 2, 5, {1, 0, 1, 0, 0, 1}},
        {9, 3, 2, {1, 0, 1}}, {27, 3, 3, {1, 2, 0, 1}}, {25, 5, 2, {2, 1, 1}}};
    int p = 0, m = 0; const int *poly = NULL;
    for (int i = 0; i < 7; i++) if (F[i].q == qq) { p = F[i].p; m = F[i].m; poly = F[i].poly; }
    if (!p) {
        for (int d = 2; d * d <= qq; d++) if (qq % d == 0) return 0;
        for (int a = 0; a < qq; a++) for (int b = 0; b < qq; b++) { add_[a][b] = (a + b) % qq; mul_[a][b] = a * b % qq; }
        return 1;
    }
    for (int a = 0; a < qq; a++)
        for (int b = 0; b < qq; b++) {
            int da[8], db[8], s = 0, pw = 1, prod[16] = {0};
            for (int i = 0, x = a, y = b; i < m; i++, x /= p, y /= p) { da[i] = x % p; db[i] = y % p; }
            for (int i = 0; i < m; i++) { s += ((da[i] + db[i]) % p) * pw; pw *= p; }
            add_[a][b] = s;
            for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) prod[i + j] = (prod[i + j] + da[i] * db[j]) % p;
            for (int d = 2 * m - 2; d >= m; d--)
                if (prod[d]) { int c = prod[d]; prod[d] = 0; for (int i = 0; i < m; i++) prod[d - m + i] = ((prod[d - m + i] - c * poly[i]) % p + p) % p; }
            s = 0; pw = 1;
            for (int i = 0; i < m; i++) { s += prod[i] * pw; pw *= p; }
            mul_[a][b] = s;
        }
    return 1;
}

static void lines(void) {  /* as cphf3x.c: line id = dir * q + off, so the direction of line L is L / q */
    int nls[MAXP] = {0};
    NL = 0;
    for (int dir = 0; dir <= q; dir++)
        for (int off = 0; off < q; off++, NL++) {
            int dx = dir < q ? 1 : 0, dy = dir < q ? dir : 1;
            int ax = dir < q ? 0 : off, ay = dir < q ? off : 0;
            memset(linemask[NL], 0, sizeof linemask[NL]);
            for (int t = 0; t < q; t++) {
                int x = add_[ax][mul_[t][dx]], y = add_[ay][mul_[t][dy]], p = x * q + y;
                ptson[NL][t] = p;
                linemask[NL][p >> 6] |= 1ULL << (p & 63);
                linesat[p][nls[p]++] = NL;
            }
            for (int i = 0; i < q; i++)
                for (int j = 0; j < q; j++) if (i != j) pairline[ptson[NL][i] * P + ptson[NL][j]] = (uint16_t)NL;
        }
    for (int x = 0; x < P; x++)
        for (int y = 0; y < P; y++) dirtab[x * P + y] = (uint8_t)(x == y ? q + 1 : pairline[x * P + y] / q);
}

/* ---------------------------------------------------------------- array */
static int k, maxk;
static uint16_t *H[MAXN], *BEST[MAXN];
static int bestk, best_is_current;

/* ---------------------------------------------------------------- classes, one level per row */
static int *IDX[MAXN + 1], *GST[MAXN + 1];
static long CAPI[MAXN + 1], CAPG[MAXN + 1];
static long NE[MAXN + 1], NG[MAXN + 1];
static long long NPAIRS[MAXN + 1];
static uint8_t *TMPD;

static void grow(int lev, long ne, long ng) {
    if (ne > CAPI[lev]) {
        CAPI[lev] = ne + ne / 2 + 4096;
        IDX[lev] = realloc(IDX[lev], sizeof(int) * CAPI[lev]);
        if (!IDX[lev]) { fprintf(stderr, "out of memory\n"); exit(3); }
    }
    if (ng + 1 > CAPG[lev]) {
        CAPG[lev] = ng + ng / 2 + 4096;
        GST[lev] = realloc(GST[lev], sizeof(int) * CAPG[lev]);
        if (!GST[lev]) { fprintf(stderr, "out of memory\n"); exit(3); }
    }
}

static void level0(void) {
    grow(0, k, 1);
    for (int c = 0; c < k; c++) IDX[0][c] = c;
    GST[0][0] = 0; GST[0][1] = k;
    NG[0] = k >= 2; NE[0] = k; NPAIRS[0] = (long long)k * (k - 1) / 2;
    if (!NG[0]) NE[0] = 0;
}

/* classes of level r split by point x in row r -> level r + 1; returns the pairs left (with STAR copies) */
static long long refine(int r, int x) {
    const uint8_t *dt = dirtab + (size_t)x * P;
    const uint16_t *Hr = H[r];
    int lev = r + 1;
    long ne = 0, ng = 0;
    long long pairs = 0;
    for (long g = 0; g < NG[r]; g++) {
        const int *src = IDX[r] + GST[r][g];
        int sz = GST[r][g + 1] - GST[r][g];
        int cnt[MAXQ + 2];
        memset(cnt, 0, sizeof(int) * (q + 2));
        for (int i = 0; i < sz; i++) { uint8_t d = dt[Hr[src[i]]]; TMPD[i] = d; cnt[d]++; }
        int ns = cnt[q + 1], off[MAXQ + 1], pos[MAXQ + 1], nemit = 0, any = 0;
        long need = 0;
        for (int d = 0; d <= q; d++) {
            if (cnt[d]) any = 1;
            if (cnt[d] && cnt[d] + ns >= 2) { off[d] = (int)need; need += cnt[d] + ns; nemit++; } else off[d] = -1;
        }
        int staronly = ns >= 2 && !any, sbase = (int)need;
        if (staronly) { need += ns; nemit++; }
        if (!nemit) continue;
        grow(lev, ne + need, ng + nemit);
        int *dst = IDX[lev] + ne;
        for (int d = 0; d <= q; d++) pos[d] = off[d];
        int sp = sbase;
        for (int i = 0; i < sz; i++) {
            int d = TMPD[i];
            if (d <= q) { if (off[d] >= 0) dst[pos[d]++] = src[i]; }
            else {
                for (int e = 0; e <= q; e++) if (off[e] >= 0) dst[pos[e]++] = src[i];
                if (staronly) dst[sp++] = src[i];
            }
        }
        for (int d = 0; d <= q; d++)
            if (off[d] >= 0) { long s = cnt[d] + ns; GST[lev][ng++] = (int)(ne + off[d]); pairs += s * (s - 1) / 2; }
        if (staronly) { GST[lev][ng++] = (int)(ne + sbase); pairs += (long long)ns * (ns - 1) / 2; }
        ne += need;
    }
    grow(lev, ne, ng);
    GST[lev][ng] = (int)ne;
    NG[lev] = ng; NE[lev] = ne; NPAIRS[lev] = pairs;
    return pairs;
}

/* pairs of level r that point x in row r leaves, counted without writing level r + 1 */
static long long count_pairs(int r, int x) {
    const uint8_t *dt = dirtab + (size_t)x * P;
    const uint16_t *Hr = H[r];
    long long pairs = 0;
    for (long g = 0; g < NG[r]; g++) {
        const int *src = IDX[r] + GST[r][g];
        int sz = GST[r][g + 1] - GST[r][g], cnt[MAXQ + 2];
        memset(cnt, 0, sizeof(int) * (q + 2));
        for (int i = 0; i < sz; i++) cnt[dt[Hr[src[i]]]]++;
        int ns = cnt[q + 1], any = 0;
        for (int d = 0; d <= q; d++) if (cnt[d]) { any = 1; if (cnt[d] + ns >= 2) { long s = cnt[d] + ns; pairs += s * (s - 1) / 2; } }
        if (!any) pairs += (long long)ns * (ns - 1) / 2;
    }
    return pairs;
}

/* cost of scoring every point of row r (evalall): per class the cheaper of pair listing and line counts */
static long long evalcost(int r) {
    long long c = 0;
    for (long g = 0; g < NG[r]; g++) {
        long sz = GST[r][g + 1] - GST[r][g], a = (long)q * sz * (sz - 1) / 2, b = (long)(q + 1) * sz + (long)q * NL + P;
        c += a < b ? a : b;
    }
    return c + P;
}

/* EV[x] = pairs of level r left after point x in row r, for every x */
static long long EV[MAXP];
static int mL[MAXL], mP[MAXP];
static void evalall(int r) {
    const uint16_t *Hr = H[r];
    long long call = 0;
    memset(EV, 0, sizeof(long long) * P);
    for (long g = 0; g < NG[r]; g++) {
        const int *m = IDX[r] + GST[r][g];
        int sz = GST[r][g + 1] - GST[r][g];
        if ((long)q * sz * (sz - 1) / 2 <= (long)(q + 1) * sz + (long)q * NL + P) {
            for (int i = 0; i < sz; i++) {
                int pa = Hr[m[i]];
                for (int j = i + 1; j < sz; j++) {
                    int pb = Hr[m[j]];
                    if (pa == pb) { call++; continue; }
                    const int *pts = ptson[pairline[pa * P + pb]];
                    for (int t = 0; t < q; t++) EV[pts[t]]++;
                }
            }
        } else {
            for (int i = 0; i < sz; i++) {
                int p = Hr[m[i]];
                mP[p]++;
                for (int l = 0; l <= q; l++) mL[linesat[p][l]]++;
            }
            for (int L = 0; L < NL; L++) {
                if (mL[L] >= 2) { long long c2 = (long long)mL[L] * (mL[L] - 1) / 2; for (int t = 0; t < q; t++) EV[ptson[L][t]] += c2; }
                mL[L] = 0;
            }
            for (int p = 0; p < P; p++) {
                if (mP[p] >= 2) EV[p] -= (long long)q * mP[p] * (mP[p] - 1) / 2;
                mP[p] = 0;
            }
        }
    }
    if (call) for (int x = 0; x < P; x++) EV[x] += call;
    if (getenv("PQ_DEBUGEVAL")) {  /* test: every score again by listing the pairs */
        static long long E2[MAXP];
        long long c2 = 0;
        memset(E2, 0, sizeof(long long) * P);
        for (long g = 0; g < NG[r]; g++) {
            const int *m = IDX[r] + GST[r][g];
            int sz = GST[r][g + 1] - GST[r][g];
            for (int i = 0; i < sz; i++)
                for (int j = i + 1; j < sz; j++) {
                    int pa = Hr[m[i]], pb = Hr[m[j]];
                    if (pa == pb) { c2++; continue; }
                    const int *pts = ptson[pairline[pa * P + pb]];
                    for (int t = 0; t < q; t++) E2[pts[t]]++;
                }
        }
        for (int x = 0; x < P; x++)
            if (E2[x] + c2 != EV[x]) { fprintf(stderr, "evalall mismatch at level %d x %d: %lld vs %lld\n", r, x, EV[x], E2[x] + c2); exit(4); }
        fprintf(stderr, "evalall level %d ok (%ld classes)\n", r, NG[r]);
    }
}

/* the last two rows exactly (masks): 1 and *bx, *by when some (x, y) leaves no pair */
static uint64_t *F2;  /* P * W */
static uint8_t FX[MAXP];
static int exact2(int *bx, int *by) {
    int r = n - 2;
    const uint16_t *Ha = H[r], *Hb = H[r + 1];
    uint64_t FY[MAXW] = {0};
    memset(F2, 0, sizeof(uint64_t) * P * W);
    memset(FX, 0, P);
    for (long g = 0; g < NG[r]; g++) {
        const int *m = IDX[r] + GST[r][g];
        int sz = GST[r][g + 1] - GST[r][g];
        for (int i = 0; i < sz; i++)
            for (int j = i + 1; j < sz; j++) {
                int pa = Ha[m[i]], pb = Ha[m[j]], qa = Hb[m[i]], qb = Hb[m[j]];
                if (pa == pb) {
                    if (qa == qb) return 0;
                    const uint64_t *lm = linemask[pairline[qa * P + qb]];
                    for (int w = 0; w < W; w++) FY[w] |= lm[w];
                } else {
                    const int *pts = ptson[pairline[pa * P + pb]];
                    if (qa == qb) { for (int t = 0; t < q; t++) FX[pts[t]] = 1; }
                    else {
                        const uint64_t *lm = linemask[pairline[qa * P + qb]];
                        for (int t = 0; t < q; t++) { uint64_t *f = F2 + (size_t)pts[t] * W; for (int w = 0; w < W; w++) f[w] |= lm[w]; }
                    }
                }
            }
    }
    int x0 = (int)(rnd() % (uint64_t)P);
    for (int i = 0; i < P; i++) {
        int x = (x0 + i) % P;
        if (FX[x]) continue;
        uint64_t fr[MAXW];
        int nf = 0;
        for (int w = 0; w < W; w++) {
            fr[w] = ~(F2[(size_t)x * W + w] | FY[w]);
            if (w == W - 1 && (P & 63)) fr[w] &= (1ULL << (P & 63)) - 1;
            nf += __builtin_popcountll(fr[w]);
        }
        if (!nf) continue;
        int pick = (int)(rnd() % (uint64_t)nf);
        for (int w = 0; w < W; w++)
            for (uint64_t v = fr[w]; v; v &= v - 1)
                if (pick-- == 0) { *bx = x; *by = w * 64 + __builtin_ctzll(v); return 1; }
    }
    return 0;
}

/* the last two rows by counts: the fewest pairs any (x, y) leaves (with STAR copies), and that (x, y) */
static uint32_t *C2;  /* P * P */
static int exact2count(int *bx, int *by) {
    int r = n - 2;
    const uint16_t *Ha = H[r], *Hb = H[r + 1];
    static int CX[MAXP], CY[MAXP];
    int c0 = 0;
    memset(C2, 0, sizeof(uint32_t) * P * P);
    memset(CX, 0, sizeof(int) * P); memset(CY, 0, sizeof(int) * P);
    for (long g = 0; g < NG[r]; g++) {
        const int *m = IDX[r] + GST[r][g];
        int sz = GST[r][g + 1] - GST[r][g];
        for (int i = 0; i < sz; i++)
            for (int j = i + 1; j < sz; j++) {
                int pa = Ha[m[i]], pb = Ha[m[j]], qa = Hb[m[i]], qb = Hb[m[j]];
                if (pa == pb) {
                    if (qa == qb) c0++;
                    else { const int *pt = ptson[pairline[qa * P + qb]]; for (int t = 0; t < q; t++) CY[pt[t]]++; }
                } else {
                    const int *pts = ptson[pairline[pa * P + pb]];
                    if (qa == qb) { for (int t = 0; t < q; t++) CX[pts[t]]++; }
                    else {
                        const int *pt = ptson[pairline[qa * P + qb]];
                        for (int t = 0; t < q; t++) { uint32_t *c = C2 + (size_t)pts[t] * P; for (int u = 0; u < q; u++) c[pt[u]]++; }
                    }
                }
            }
    }
    long best = 1L << 40; int ties = 0;
    for (int x = 0; x < P; x++)
        for (int y = 0; y < P; y++) {
            long v = (long)c0 + CX[x] + CY[y] + C2[(size_t)x * P + y];
            if (v < best) { best = v; *bx = x; *by = y; ties = 1; }
            else if (v == best && rnd() % (uint64_t)++ties == 0) { *bx = x; *by = y; }
        }
    return (int)(best > 1000000 ? 1000000 : best);
}

/* ---------------------------------------------------------------- one column */
static int cand[MAXN], nearcand[MAXN], tracking, bestviol;
static long long cap2, evalt;
static int leaves, leafmax, branch, blast, ntrack, cheap, nsample, topm;
static long long evalc;
static long long st_attempts, st_leaves, st_ok, st_repair, st_drop;

static int dfs(int r) {
    if (NPAIRS[r] == 0) { for (int s = r; s < n; s++) cand[s] = (int)(rnd() % (uint64_t)P); return 1; }
    if (r == n - 2) {
        if (NPAIRS[r] > cap2 || leaves >= leafmax) return 0;
        leaves++; st_leaves++;
        int x, y;
        if (exact2(&x, &y)) { cand[r] = x; cand[r + 1] = y; return 1; }
        if (tracking && NPAIRS[r] <= cap2 / 2) {
            int v = exact2count(&x, &y);
            if (v < bestviol) { bestviol = v; memcpy(nearcand, cand, sizeof(int) * r); nearcand[r] = x; nearcand[r + 1] = y; }
        }
        return 0;
    }
    /* scoring every point picks the same points on every attempt, so the top rows (large classes, where any point
       is about as good) take random points for diversity: the rule NPAIRS * q > evalt; PQ_EVALC=C instead scores
       every row whose scoring costs at most C (later attempts) */
    if (cheap || evalc <= 0 ? NPAIRS[r] * q > evalt : evalcost(r) > evalc) {
        /* scoring every point costs too much here: the best of nsample random points (1 = any point; with large
           classes every point is about as good) */
        int x = (int)(rnd() % (uint64_t)P), ns = cheap ? 1 : nsample;
        if (ns > 1) {
            long long bv = count_pairs(r, x);
            for (int s = 1; s < ns; s++) {
                int y = (int)(rnd() % (uint64_t)P);
                long long v = count_pairs(r, y);
                if (v < bv) { bv = v; x = y; }
            }
        }
        cand[r] = x; refine(r, x);
        return dfs(r + 1);
    }
    evalall(r);
    int nb = r == n - 3 ? blast : branch;  /* more children just above the exact rows: they are cheap there */
    if (nb > 16) nb = 16;
    if (nb < 1) nb = 1;
    int bx[16];
    long long bv[16];
    /* the M smallest scores (M = topm above the rows next to the exact pair, else nb), then nb of them in random
       order: diversity between attempts where scores differ little */
    int M = r == n - 3 ? nb : (topm > nb ? topm : nb);
    if (M > 64) M = 64;
    int cx[64];
    long long cv[64];
    for (int i = 0; i < M; i++) { cx[i] = -1; cv[i] = 1LL << 62; }
    int x0 = (int)(rnd() % (uint64_t)P);
    for (int i = 0; i < P; i++) {  /* random among equals by the random start */
        int x = (x0 + i) % P;
        long long v = EV[x];
        if (v >= cv[M - 1]) continue;
        int j = M - 1;
        while (j > 0 && cv[j - 1] > v) { cv[j] = cv[j - 1]; cx[j] = cx[j - 1]; j--; }
        cv[j] = v; cx[j] = x;
    }
    if (M > nb) for (int i = 0; i < nb; i++) {  /* partial shuffle: nb random of the M */
        int j = i + (int)(rnd() % (uint64_t)(M - i));
        int tx = cx[i]; cx[i] = cx[j]; cx[j] = tx;
        long long tv = cv[i]; cv[i] = cv[j]; cv[j] = tv;
    }
    for (int i = 0; i < nb; i++) { bx[i] = cx[i]; bv[i] = cv[i]; }
    for (int i = 0; i < nb; i++) {
        if (bx[i] < 0) break;
        cand[r] = bx[i]; refine(r, bx[i]);
        if (dfs(r + 1)) return 1;
        if (leaves >= leafmax) return 0;
    }
    return 0;
}

static int tries, maxviol;
static int find_column(void) {
    bestviol = 1 << 30;
    for (int t = 0; t < tries; t++) {
        /* the first attempt is cheap (random points while classes are large: enough while columns are easy to
           find); later attempts score every point wherever that costs at most evalc */
        cheap = t == 0;
        tracking = maxviol > 0 && t >= tries - ntrack;
        leaves = 0; st_attempts++;
        level0();
        if (dfs(0)) { st_ok++; return 1; }
    }
    return 0;
}

/* ---------------------------------------------------------------- array edits */
static void snapshot(void) {  /* before any removal from the best array */
    if (!best_is_current) return;
    for (int r = 0; r < n; r++) memcpy(BEST[r], H[r], sizeof(uint16_t) * k);
    best_is_current = 0;
}

static void append(const int *v) {
    for (int r = 0; r < n; r++) H[r][k] = (uint16_t)v[r];
    k++;
    if (k > bestk) { bestk = k; best_is_current = 1; }
}

static uint8_t *gone;
static void compact(void) {
    int m = 0;
    for (int c = 0; c < k; c++) if (!gone[c]) { if (m != c) for (int r = 0; r < n; r++) H[r][m] = H[r][c]; m++; }
    memset(gone, 0, (size_t)k);
    k = m;
}

/* add nearcand; remove a greedy cover of the pairs it leaves */
static void repair(void) {
    level0();
    for (int r = 0; r < n; r++) refine(r, nearcand[r]);
    long np = 0, cap = 64;
    int *pa = malloc(sizeof(int) * cap), *pb = malloc(sizeof(int) * cap);
    for (long g = 0; g < NG[n]; g++) {
        const int *m = IDX[n] + GST[n][g];
        int sz = GST[n][g + 1] - GST[n][g];
        for (int i = 0; i < sz; i++)
            for (int j = i + 1; j < sz; j++) {
                int a = m[i] < m[j] ? m[i] : m[j], b = m[i] < m[j] ? m[j] : m[i], dup = 0;
                for (long e = 0; e < np && !dup; e++) dup = pa[e] == a && pb[e] == b;
                if (dup) continue;
                if (np == cap) { cap *= 2; pa = realloc(pa, sizeof(int) * cap); pb = realloc(pb, sizeof(int) * cap); }
                pa[np] = a; pb[np] = b; np++;
            }
    }
    snapshot();
    for (;;) {  /* the column in the most uncovered pairs, random among equals */
        int bc = -1, bd = 0, ties = 0;
        for (long e = 0; e < np; e++)
            for (int s = 0; s < 2; s++) {
                int c = s ? pb[e] : pa[e];
                if (c < 0 || gone[c]) continue;
                int d = 0;
                for (long f = 0; f < np; f++) if (pa[f] >= 0 && (pa[f] == c || pb[f] == c)) d++;
                if (d > bd) { bd = d; bc = c; ties = 1; }
                else if (d == bd && c != bc && rnd() % (uint64_t)++ties == 0) bc = c;
            }
        if (bc < 0) break;
        gone[bc] = 1;
        for (long f = 0; f < np; f++) if (pa[f] >= 0 && (pa[f] == bc || pb[f] == bc)) { pa[f] = -1; pb[f] = -1; }
    }
    free(pa); free(pb);
    compact();
    append(nearcand);
}

static void drop(void) {
    snapshot();
    int d = 1 + (int)(rnd() % 3);
    for (int i = 0; i < d && k > 0; i++) gone[rnd() % (uint64_t)k] = 1;
    compact();
}

/* ---------------------------------------------------------------- output */
static const char *OUT;
static double t0;
static void write_best(const char *why) {
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s.tmp", OUT);
    FILE *f = fopen(tmp, "w");
    if (!f) { perror(tmp); return; }
    uint16_t **A = best_is_current ? H : BEST;
    fprintf(f, "best k %d (q %d, n %d, %.0f s, pq_cphf3big, %s)\n", bestk, q, n, cpu() - t0, why);
    char *line = malloc((size_t)bestk * 7 + 16);
    for (int r = 0; r < n; r++) {
        char *s = line;
        for (int c = 0; c < bestk; c++) {
            int v = A[r][c];
            if (c) *s++ = ' ';
            char b[8]; int l = 0;
            do { b[l++] = (char)('0' + v % 10); v /= 10; } while (v);
            while (l) *s++ = b[--l];
        }
        *s++ = '\n';
        fwrite(line, 1, (size_t)(s - line), f);
    }
    free(line);
    if (fclose(f) == 0) rename(tmp, OUT);
}

static volatile sig_atomic_t stop_flag;
static void on_signal(int s) { (void)s; stop_flag = 1; }

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: pq_cphf3big q n maxk cpu_seconds seed OUT [stall_seconds] [maxviol] [tries]\n");
        return 2;
    }
    q = atoi(argv[1]); n = atoi(argv[2]); maxk = atoi(argv[3]);
    double secs = atof(argv[4]);
    rng = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[5]) * 0xD1B54A32D192ED03ULL;
    if (!rng) rng = 1;
    OUT = argv[6];
    double stall = argc > 7 ? atof(argv[7]) : 1e30;
    maxviol = argc > 8 ? atoi(argv[8]) : 3;
    tries = argc > 9 ? atoi(argv[9]) : 16;
    if (q < 2 || q > MAXQ || n < 3 || n > MAXN || maxk < 3 || maxk > MAXK || !field(q)) {
        fprintf(stderr, "need a supported prime power q <= %d, 3 <= n <= %d, maxk <= %d\n", MAXQ, MAXN, MAXK);
        return 2;
    }
    P = q * q; W = (P + 63) / 64;
    pairline = calloc((size_t)P * P, sizeof(uint16_t));
    dirtab = calloc((size_t)P * P, 1);
    F2 = malloc(sizeof(uint64_t) * P * W);
    C2 = malloc(sizeof(uint32_t) * P * P);
    lines();
    for (int r = 0; r < n; r++) {
        H[r] = malloc(sizeof(uint16_t) * (maxk + 2));
        BEST[r] = malloc(sizeof(uint16_t) * (maxk + 2));
    }
    TMPD = malloc((size_t)maxk + 2);
    gone = calloc((size_t)maxk + 2, 1);
    /* the two exact rows are tried only when the pairs left could still be separated: a pair survives a random
       (x, y) with probability (1-p)^2, p = (1 - 1/q^2)(1 - 1/q); some (x, y) of the q^4 is free while about
       pairs * (1-p)^2 < 4 ln q. cap2 = 4 times that (counts only under half of it). */
    {
        double p = (1.0 - 1.0 / P) * (1.0 - 1.0 / q);
        cap2 = (long long)(4.0 * 4.0 * log((double)q) / ((1 - p) * (1 - p)));
        if (getenv("PQ_CAP2")) cap2 = atoll(getenv("PQ_CAP2"));
        evalt = getenv("PQ_EVALT") ? atoll(getenv("PQ_EVALT")) : 4000000LL;
    }
    leafmax = getenv("PQ_LEAFMAX") ? atoi(getenv("PQ_LEAFMAX")) : 32;
    branch = getenv("PQ_BRANCH") ? atoi(getenv("PQ_BRANCH")) : 2;
    blast = getenv("PQ_BLAST") ? atoi(getenv("PQ_BLAST")) : 8;
    ntrack = getenv("PQ_NTRACK") ? atoi(getenv("PQ_NTRACK")) : 4;
    evalc = getenv("PQ_EVALC") ? atoll(getenv("PQ_EVALC")) : 0;
    topm = getenv("PQ_TOPM") ? atoi(getenv("PQ_TOPM")) : 1;
    nsample = getenv("PQ_SAMPLE") ? atoi(getenv("PQ_SAMPLE")) : 1;
    if (getenv("PQ_BENCH")) {  /* search efficiency on a fixed array: columns found per CPU second, nothing changed */
        double b0 = cpu(), secs_b = atof(getenv("PQ_BENCH"));
        long cols = 0, found = 0;
        long long l0 = 0;
        const char *sfb = getenv("PQ_START");
        if (!sfb) { fprintf(stderr, "PQ_BENCH needs PQ_START\n"); return 2; }
        FILE *f = fopen(sfb, "r");
        int k0;
        if (!f || fscanf(f, "best k %d", &k0) != 1 || k0 > maxk || fscanf(f, "%*[^\n]") < 0) { fprintf(stderr, "bad PQ_START\n"); return 2; }
        for (int r = 0; r < n; r++) for (int c = 0; c < k0; c++) { unsigned v; if (fscanf(f, "%u", &v) != 1) return 2; H[r][c] = (uint16_t)v; }
        fclose(f);
        k = k0;
        while (cpu() - b0 < secs_b) { cols++; l0 = st_leaves; if (find_column()) found++; (void)l0; }
        double el = cpu() - b0;
        printf("bench q %d n %d k %d: %ld column searches, %ld found (%.4f), %.4f found/s, attempts %lld leaves %lld, %.1f ms per search\n",
               q, n, k, cols, found, (double)found / cols, found / el, st_attempts, st_leaves, 1000 * el / cols);
        return 0;
    }
    k = 0;
    const char *sf = getenv("PQ_START");
    if (sf) {
        FILE *f = fopen(sf, "r");
        int k0;
        if (!f || fscanf(f, "best k %d", &k0) != 1 || k0 < 0 || k0 > maxk || fscanf(f, "%*[^\n]") < 0) {
            fprintf(stderr, "bad PQ_START file\n"); return 2;
        }
        for (int r = 0; r < n; r++)
            for (int c = 0; c < k0; c++) {
                unsigned v;
                if (fscanf(f, "%u", &v) != 1 || v >= (unsigned)P) { fprintf(stderr, "bad PQ_START file\n"); return 2; }
                H[r][c] = (uint16_t)v;
            }
        fclose(f);
        k = k0;
    }
    bestk = k; best_is_current = 1;
    signal(SIGTERM, on_signal); signal(SIGINT, on_signal);
    t0 = cpu();
    double last_write = t0, last_best_t = t0, last_log = t0;
    int written_k = -1, last_bestk = bestk;
    fprintf(stderr, "pq_cphf3big q %d n %d maxk %d start k %d cap2 %lld evalt %lld tries %d maxviol %d\n",
            q, n, maxk, k, cap2, evalt, tries, maxviol);
    const char *why = "time";
    while (!stop_flag) {
        double now = cpu();
        if (now - t0 >= secs) { why = "time"; break; }
        if (bestk >= maxk) { why = "maxk"; break; }
        if (now - last_best_t >= stall) { why = "stall"; break; }
        if (find_column()) append(cand);
        else if (maxviol > 0 && bestviol <= maxviol) { repair(); st_repair++; }
        else { drop(); st_drop++; }
        if (bestk > last_bestk) { last_bestk = bestk; last_best_t = cpu(); }
        now = cpu();
        if (now - last_log >= 30) {
            fprintf(stderr, "%8.0f s  k %d  best %d  attempts %lld  ok %lld  leaves %lld  repairs %lld  drops %lld\n",
                    now - t0, k, bestk, st_attempts, st_ok, st_leaves, st_repair, st_drop);
            last_log = now;
        }
        if (now - last_write >= 60 && bestk != written_k) { write_best("checkpoint"); written_k = bestk; last_write = now; }
    }
    if (stop_flag) why = "signal";
    write_best(why);
    fprintf(stderr, "done (%s): best k %d after %.0f s CPU; attempts %lld ok %lld leaves %lld repairs %lld drops %lld\n",
            why, bestk, cpu() - t0, st_attempts, st_ok, st_leaves, st_repair, st_drop);
    return 0;
}
