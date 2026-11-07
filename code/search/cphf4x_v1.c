/* Sherwood covering perfect hash families of strength 4: SCPHF(n; k, q^3, 4), an n x k array of points of AG(3,q) in
   which any four columns hold, in some row, four points not on one plane. It gives CA(n(q^4 - q) + q; 4, k, q): row
   u = (u0, u1, u2, u3) of block r puts u0 + u1 x + u2 y + u3 z in a column whose point in row r is (x, y, z), the q
   constant rows once (Sherwood, Martirosyan and Colbourn 2006).
   Search as cphf3x.c, one dimension up: grow column by column; a new column must, for every triple of old columns,
   avoid in some row the plane through the triple's three points there (every point, where they are collinear or
   coincide). Triples are never all stored. A first-row point p0 spoils the triples whose first-row points lie with
   p0 on one plane: listed from the columns on each of the q^2 + q + 1 planes through p0 (about k^3 / 6q) and
   streamed, keeping only the triples a second-row point p1 also spoils (a determinant test). Later rows filter; the
   last row needs a point off the union of the remaining planes. When no column fits: least-conflict swap or random
   drops.
   Prints "best k K (q Q, n N, t 4, S s)", then the array (n lines of k point ids (x q + y) q + z).
   cc -O3 -o cphf4x cphf4x.c && ./cphf4x q n seconds seed [maxk] [tries] [maxviol] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 25
#define MAXN 12
#define ALL 0xFFFFFFFFu

static int q, P, n, NN, NPL, Wq;
static int add[MAXQ][MAXQ], mul[MAXQ][MAXQ], sub[MAXQ][MAXQ], inv[MAXQ];
static uint8_t *px, *py, *pz;      /* coordinates of each point */
static int nv[MAXQ * MAXQ + MAXQ + 1][3];  /* canonical normal of each direction class */
static uint64_t *pmask;            /* plane masks, NPL x Wq */
static uint16_t *H[MAXN], *best[MAXN];
static uint64_t rng;

static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static int field(int qq) {  /* GF(q) tables, elements as base-p digit vectors, multiplication modulo a fixed
                               irreducible polynomial (coefficients low degree first, monic, degree m) */
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

static int dirclass(int a, int b, int c) {  /* index of the nonzero vector's class: first nonzero coordinate 1 */
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
}

/* first-row incidence, rebuilt for each extension: the columns on each plane */
static int k;
static int *qstart, *qlist;
static uint64_t *stk, *stkend;

static uint64_t T3(int a, int b, int c) { return (uint64_t)a << 32 | (uint64_t)b << 16 | (uint64_t)c; }
#define TA(t) ((int)((t) >> 32))
#define TB(t) ((int)((t) >> 16 & 0xFFFF))
#define TC(t) ((int)((t) & 0xFFFF))

static void incidence(void) {
    memset(qstart, 0, sizeof(int) * (NPL + 1));
    for (int c = 0; c < k; c++) for (int i = 0; i < NN; i++) qstart[i * q + dot(i, H[0][c]) + 1]++;
    for (int i = 0; i < NPL; i++) qstart[i + 1] += qstart[i];
    int *fill = malloc(sizeof(int) * NPL);
    memcpy(fill, qstart, sizeof(int) * NPL);
    for (int c = 0; c < k; c++) for (int i = 0; i < NN; i++) qlist[fill[i * q + dot(i, H[0][c])]++] = c;
    free(fill);
}

static int badrow(int r, uint64_t t, int p) {  /* p on the plane (or line, or point) of the triple's row-r points */
    int A = H[r][TA(t)], B = H[r][TB(t)], C = H[r][TC(t)];
    int u1 = sub[px[B]][px[A]], u2 = sub[py[B]][py[A]], u3 = sub[pz[B]][pz[A]];
    int v1 = sub[px[C]][px[A]], v2 = sub[py[C]][py[A]], v3 = sub[pz[C]][pz[A]];
    int w1 = sub[px[p]][px[A]], w2 = sub[py[p]][py[A]], w3 = sub[pz[p]][pz[A]];
    int c1 = sub[mul[v2][w3]][mul[v3][w2]], c2 = sub[mul[v3][w1]][mul[v1][w3]], c3 = sub[mul[v1][w2]][mul[v2][w1]];
    return add[add[mul[u1][c1]][mul[u2][c2]]][mul[u3][c3]] == 0;  /* det(B - A, C - A, p - A) */
}

static uint32_t rowplane(int r, uint64_t t) { return plane3(H[r][TA(t)], H[r][TB(t)], H[r][TC(t)]); }

/* Triples spoiled in row 0 by p0 (their points and p0 lie on one plane, so on a plane through p0; a triple whose
   points and p0 are collinear is listed once per plane through that line, harmless) and in row 1 by p1:
   det(B1 - A1, C1 - A1, p1 - A1) = (C1 - A1) . ((p1 - A1) x (B1 - A1)), the cross product kept per pair. */
static long level1(int p0, int p1, uint64_t *out) {
    long m = 0, room = stkend - out;
    for (int d = 0; d < NN; d++) {
        int pl = d * q + dot(d, p0), s = qstart[pl], e = qstart[pl + 1];
        for (int i = s; i < e; i++) {
            int a = qlist[i], A1 = H[1][a];
            int w1 = sub[px[p1]][px[A1]], w2 = sub[py[p1]][py[A1]], w3 = sub[pz[p1]][pz[A1]];
            for (int j = i + 1; j < e; j++) {
                int b = qlist[j], B1 = H[1][b];
                int u1 = sub[px[B1]][px[A1]], u2 = sub[py[B1]][py[A1]], u3 = sub[pz[B1]][pz[A1]];
                int z1 = sub[mul[w2][u3]][mul[w3][u2]], z2 = sub[mul[w3][u1]][mul[w1][u3]], z3 = sub[mul[w1][u2]][mul[w2][u1]];
                for (int l = j + 1; l < e; l++) {
                    int C1 = H[1][qlist[l]];
                    if (add[add[mul[sub[px[C1]][px[A1]]][z1]][mul[sub[py[C1]][py[A1]]][z2]]][mul[sub[pz[C1]][pz[A1]]][z3]] == 0) {
                        if (m == room) return -1;
                        out[m++] = T3(a, b, qlist[l]);
                    }
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
static int *cnt;

static int dfs(int r, uint64_t *act, long na) {  /* act: triples spoiled in every row before r */
    if (r == n - 1) {
        uint64_t *u = calloc(Wq, sizeof(uint64_t));
        for (long i = 0; i < na; i++) {
            uint32_t id = rowplane(r, act[i]);
            if (id == ALL) { free(u); return 0; }
            for (int w = 0; w < Wq; w++) u[w] |= pmask[(size_t)id * Wq + w];
        }
        int free_ = 0;
        for (int p = 0; p < P; p++) free_ += !(u[p >> 6] >> (p & 63) & 1);
        if (!free_) {
            if (na <= minviol) {  /* least-conflict point: on the fewest of the remaining planes */
                memset(cnt, 0, sizeof(int) * P);
                for (long i = 0; i < na; i++) {
                    uint32_t id = rowplane(r, act[i]);
                    for (int w = 0; w < Wq; w++)
                        for (uint64_t x = pmask[(size_t)id * Wq + w]; x; x &= x - 1) cnt[w * 64 + __builtin_ctzll(x)]++;
                }
                int bp = -1, bc = (int)na + 1, ties = 0;
                for (int p = 0; p < P; p++)
                    if (cnt[p] < bc) { bc = cnt[p]; bp = p; ties = 1; }
                    else if (cnt[p] == bc && rnd() % ++ties == 0) bp = p;
                if (bc < minviol) { minviol = bc; memcpy(mincand, cand, sizeof cand); mincand[r] = (uint16_t)bp; }
            }
            free(u);
            return 0;
        }
        int pick = (int)(rnd() % (uint64_t)free_);
        for (int p = 0; p < P; p++) if (!(u[p >> 6] >> (p & 63) & 1) && pick-- == 0) { cand[r] = (uint16_t)p; break; }
        free(u);
        return 1;
    }
    uint64_t *nxt = act + na;
    if (stkend - nxt < na) return 0;
    for (int t = 0; t < tries; t++) {
        int p = (int)(rnd() % (uint64_t)P);
        long m = 0;
        for (long i = 0; i < na; i++) if (badrow(r, act[i], p)) nxt[m++] = act[i];
        cand[r] = (uint16_t)p;
        if (dfs(r + 1, nxt, m)) return 1;
    }
    return 0;
}

static int extend(void) {
    incidence();
    minviol = 1L << 40;
    for (int t0 = 0; t0 < tries; t0++) {
        int p0 = (int)(rnd() % (uint64_t)P);
        cand[0] = (uint16_t)p0;
        for (int t1 = 0; t1 < tries; t1++) {
            int p1 = (int)(rnd() % (uint64_t)P);
            long m = level1(p0, p1, stk);
            if (m < 0) continue;
            cand[1] = (uint16_t)p1;
            if (dfs(2, stk, m)) return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: cphf4x q n seconds seed [maxk] [tries] [maxviol]\n"); return 2; }
    q = atoi(argv[1]); n = atoi(argv[2]);
    double secs = atof(argv[3]);
    rng = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[4]) * 0xD1B54A32D192ED03ULL;
    int maxk = argc > 5 ? atoi(argv[5]) : 1024;
    tries = argc > 6 ? atoi(argv[6]) : 2 * q;
    maxviol = argc > 7 ? atoi(argv[7]) : 3;
    if (q > MAXQ || n > MAXN || n < 3 || !field(q)) { fprintf(stderr, "q must be a supported prime power <= %d, n >= 3\n", MAXQ); return 2; }
    if (maxk > 65535) maxk = 65535;
    geometry();
    for (int r = 0; r < n; r++) { H[r] = malloc(sizeof(uint16_t) * (maxk + 1)); best[r] = malloc(sizeof(uint16_t) * (maxk + 1)); }
    qstart = malloc(sizeof(int) * (NPL + 1)); qlist = malloc(sizeof(int) * (size_t)(maxk + 1) * NN);
    cnt = malloc(sizeof(int) * P);
    double est = (double)maxk * maxk * maxk / (6.0 * q * q);  /* triples kept after rows 0 and 1, at maxk */
    size_t cap = (size_t)(est * 3) + (size_t)maxk * maxk + 65536;
    stk = malloc(sizeof(uint64_t) * cap); stkend = stk + cap;
    int *deg = malloc(sizeof(int) * (maxk + 1));
    uint8_t *gone = malloc(maxk + 1);
    int bestk = 0;
    clock_t t0 = clock();
    k = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && bestk < maxk) {
        if (k < maxk && extend()) {
            for (int r = 0; r < n; r++) H[r][k] = cand[r];
            k++;
            if (k > bestk) { bestk = k; for (int r = 0; r < n; r++) memcpy(best[r], H[r], sizeof(uint16_t) * k); }
        } else if (minviol <= maxviol) {  /* add the least-conflict column, then drop columns to clear its conflicts */
            long m = level1(mincand[0], mincand[1], stk), nv_ = 0;
            if (m < 0) continue;
            for (long i = 0; i < m; i++) {
                int all = 1;
                for (int r = 2; r < n && all; r++) all = badrow(r, stk[i], mincand[r]);
                if (all) stk[nv_++] = stk[i];
            }
            memset(deg, 0, sizeof(int) * k); memset(gone, 0, (size_t)k);
            for (long j = 0; j < nv_; j++) { deg[TA(stk[j])]++; deg[TB(stk[j])]++; deg[TC(stk[j])]++; }
            for (;;) {  /* greedy cover of the uncovered triples by columns to remove */
                int bc = -1, bd = 0, ties = 0;
                for (int c = 0; c < k; c++)
                    if (!gone[c] && deg[c] > bd) { bd = deg[c]; bc = c; ties = 1; }
                    else if (!gone[c] && deg[c] == bd && bd > 0 && rnd() % ++ties == 0) bc = c;
                if (bd == 0) break;
                gone[bc] = 1;
                for (long j = 0; j < nv_; j++) {
                    if (stk[j] == UINT64_MAX) continue;
                    int a = TA(stk[j]), b = TB(stk[j]), c = TC(stk[j]);
                    if (a == bc || b == bc || c == bc) { deg[a]--; deg[b]--; deg[c]--; stk[j] = UINT64_MAX; }
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
    printf("best k %d (q %d, n %d, t 4, %.0f s)\n", bestk, q, n, (double)(clock() - t0) / CLOCKS_PER_SEC);
    for (int r = 0; r < n; r++) {
        for (int c = 0; c < bestk; c++) printf(c ? " %d" : "%d", best[r][c]);
        printf("\n");
    }
    return 0;
}
