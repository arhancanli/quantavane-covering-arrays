/* Independent check of a strength-5 Sherwood CPHF (engine/native/cphf5m.c and cyc5.c output). Field arithmetic as
   in independent/scphf4_check.c (Horner multiplication modulo the listed polynomial, field axioms tested before
   use), written apart from the searches; points of AG(4,q) as ids ((x q + y) q + z) q + w.
   1. Every five columns a < b < c < d < e must hold, in some row, points A, B, C, D, E with
      det(B - A, C - A, D - A, E - A) != 0 (not on one hyperplane). The determinant is expanded along E - A: the
      cofactors are the 3 x 3 minors of B - A, C - A, D - A. Three exact methods:
      "brute" tries all C(k,5) sets.
      "cells" (for large k) lists only the sets on one hyperplane in each of the first M rows: columns are bucketed
      by every hyperplane through their point in row 0, each bucket again by every hyperplane through the point in
      row 1, and so on; a set lies on one hyperplane in each of those rows exactly when it shares a bucket at depth
      M, so the sets at depth M are tested in rows M..n-1 and no other set can fail. A failing set is counted once,
      in the bucket path of the smallest hyperplanes holding it.
      "cyclic" (hybrid) uses the rows that are affine progressions v, Tv, T^2 v, ... for an invertible affine map T
      of AG(4,q) (T solved from five consecutive points of the row in coordinates (1, x, y, z, w), then checked on
      every point). T^s maps columns j, j', ... of such a row to j + s, j' + s, ... and keeps points on or off a
      hyperplane, so a set of five columns fails in all of these rows exactly when its shift by minus its first
      column does. The sets holding column 0 that fail in all of them are found as in "cells", with hyperplanes
      through column 0's point (every set holding column 0 is tested or leaves one hyperplane in a bucketed row,
      each failing set counted once); then every shift of each is tested in the other rows. Any failing set of the
      array is such a shift, so none is missed.
      Default: brute when C(k,5) <= 1e10, else cyclic when some row is an affine progression, else cells (METHOD
      forces one; threads from CHECK_THREADS, bucketing depth from CHECK_M).
   2. Spot check of the covering array it gives, CA(n(q^5 - q) + q; 5, k, q) (row (u0,..,u4) of block r puts
      u0 + u1 x + u2 y + u3 z + u4 w in a column whose point in row r is (x, y, z, w); the q constant rows once):
      for SAMPLES random sets of five columns (default about 2e9 symbol evaluations' worth, 20 to 500), every one
      of the q^5 tuples of symbols must appear.
   cc -O3 -o scphf5_check scphf5_check.c -lpthread && ./scphf5_check q FILE [SAMPLES] [brute|cells|cyclic] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <pthread.h>
#include <unistd.h>
#include "progress.h"

static const char *ARRAY;  /* the array file (names it in a CHECK_PROGRESS header) */

#define MAXQ 32
#define MAXN 48
#define MAXK 65535

static int q, p, m;
static int poly[8];  /* low degree first, monic */
static uint8_t ADD[MAXQ][MAXQ], SUB[MAXQ][MAXQ], MUL[MAXQ][MAXQ];

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
        p = q; m = 1; poly[0] = 0; poly[1] = 1;
        for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { ADD[a][b] = (a + b) % q; MUL[a][b] = a * b % q; }
    } else {
        for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { ADD[a][b] = padd(a, b); MUL[a][b] = pmul(a, b); }
    }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) if (ADD[b][c] == a) SUB[a][b] = c;
    for (int a = 1; a < q; a++) {
        int inv = 0;
        for (int b = 1; b < q; b++) if (MUL[a][b] == 1) inv = 1;
        if (!inv) return 0;
    }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            if (MUL[a][b] != MUL[b][a] || ADD[a][b] != ADD[b][a]) return 0;
            for (int c = 0; c < q; c++)
                if (MUL[MUL[a][b]][c] != MUL[a][MUL[b][c]] || MUL[a][ADD[b][c]] != ADD[MUL[a][b]][MUL[a][c]]) return 0;
        }
    return 1;
}

static double pow_int(double b, int e) { double r = 1; while (e-- > 0) r *= b; return r; }

static int n, k;
static uint8_t *X[MAXN], *Y[MAXN], *Z[MAXN], *W[MAXN];
static int NV, NPL, M;             /* hyperplane normals (q^3 + q^2 + q + 1), hyperplanes (q NV), rows bucketed */
static uint8_t (*NA)[4];

static inline int plane_of(int i, int r, int c) {  /* id of the hyperplane with normal i through column c's point */
    return i * q + ADD[ADD[MUL[NA[i][0]][X[r][c]]][MUL[NA[i][1]][Y[r][c]]]][ADD[MUL[NA[i][2]][Z[r][c]]][MUL[NA[i][3]][W[r][c]]]];
}

static inline int det3(int a0, int a1, int a2, int b0, int b1, int b2, int c0, int c1, int c2) {
    return ADD[SUB[MUL[a0][SUB[MUL[b1][c2]][MUL[b2][c1]]]][MUL[a1][SUB[MUL[b0][c2]][MUL[b2][c0]]]]][MUL[a2][SUB[MUL[b0][c1]][MUL[b1][c0]]]];
}

/* cofactors of det[e; u; v; w] along e: N_i = (-1)^i times the minor of u, v, w without column i */
static inline void cofactors(const int *u, const int *v, const int *w, int *N) {
    N[0] = det3(u[1], u[2], u[3], v[1], v[2], v[3], w[1], w[2], w[3]);
    N[1] = SUB[0][det3(u[0], u[2], u[3], v[0], v[2], v[3], w[0], w[2], w[3])];
    N[2] = det3(u[0], u[1], u[3], v[0], v[1], v[3], w[0], w[1], w[3]);
    N[3] = SUB[0][det3(u[0], u[1], u[2], v[0], v[1], v[2], w[0], w[1], w[2])];
}

static inline void diff(int r, int a, int b, int *u) {  /* point of b minus point of a in row r */
    u[0] = SUB[X[r][b]][X[r][a]]; u[1] = SUB[Y[r][b]][Y[r][a]]; u[2] = SUB[Z[r][b]][Z[r][a]]; u[3] = SUB[W[r][b]][W[r][a]];
}

static inline int dot4(const int *N, const int *e) {
    return ADD[ADD[MUL[N[0]][e[0]]][MUL[N[1]][e[1]]]][ADD[MUL[N[2]][e[2]]][MUL[N[3]][e[3]]]];
}

static int indep(int r, int a, int b, int c, int d, int e) {
    int u[4], v[4], w[4], x[4], N[4];
    diff(r, a, b, u); diff(r, a, c, v); diff(r, a, d, w); diff(r, a, e, x);
    cofactors(u, v, w, N);
    return dot4(N, x) != 0;
}

struct tl {  /* one thread's buffers, one set per depth */
    int *pid[MAXN], *ent[MAXN], *cnt[MAXN], *off[MAXN], *touched[MAXN];
    int path[MAXN];
    int (*dv)[4];                  /* leaf: differences from the first column in row M */
    long long sets, bad, base, shifted;
    int first[5];
};

static int canonical(const struct tl *T, const int *s) {
    for (int r = 0; r < M; r++) {
        int best = INT_MAX;
        for (int i = 0; i < NV; i++) {
            int pa = plane_of(i, r, s[0]), same = pa < best;
            for (int j = 1; j < 5 && same; j++) same = plane_of(i, r, s[j]) == pa;
            if (same) best = pa;
        }
        if (best != T->path[r]) return 0;
    }
    return 1;
}

static void leaf(struct tl *T, const int *L, int len) {
    int (*dv)[4] = T->dv;
    for (int x = 0; x < len; x++) {
        int a = L[x];
        for (int j = x + 1; j < len; j++) diff(M, a, L[j], dv[j]);
        for (int y = x + 1; y < len; y++)
            for (int z = y + 1; z < len; z++)
                for (int t = z + 1; t < len; t++) {
                    int N[4];
                    cofactors(dv[y], dv[z], dv[t], N);
                    for (int u = t + 1; u < len; u++) {
                        int ok = dot4(N, dv[u]) != 0;
                        int s[5] = {a, L[y], L[z], L[t], L[u]};
                        for (int r = M + 1; r < n && !ok; r++) ok = indep(r, s[0], s[1], s[2], s[3], s[4]);
                        T->sets++;
                        if (!ok && canonical(T, s)) {
                            if (!T->bad) memcpy(T->first, s, sizeof s);
                            T->bad++;
                        }
                    }
                }
    }
}

static void rec(struct tl *T, int lev, const int *L, int len) {  /* L ascending; buckets keep the order */
    if (lev == M) { leaf(T, L, len); return; }
    int *pid = T->pid[lev], *ent = T->ent[lev], *cnt = T->cnt[lev], *off = T->off[lev], *touched = T->touched[lev];
    int nt = 0, e = 0;
    for (int x = 0; x < len; x++)
        for (int i = 0; i < NV; i++) {
            int pl = plane_of(i, lev, L[x]);
            pid[e++] = pl;
            if (cnt[pl]++ == 0) touched[nt++] = pl;
        }
    int st = 0;
    for (int t = 0; t < nt; t++) { off[touched[t]] = st; st += cnt[touched[t]]; }
    e = 0;
    for (int x = 0; x < len; x++)
        for (int i = 0; i < NV; i++) ent[off[pid[e++]]++] = L[x];
    for (int t = 0; t < nt; t++) {
        int pl = touched[t], c = cnt[pl];
        if (c >= 5) { T->path[lev] = pl; rec(T, lev + 1, ent + off[pl] - c, c); }
    }
    for (int t = 0; t < nt; t++) cnt[touched[t]] = 0;
}

static int *b0start, *b0list, nextplane;
static struct tl *TL;

static void *worker(void *arg) {
    struct tl *T = arg;
    for (;;) {
        int pl = __sync_fetch_and_add(&nextplane, 1);
        if (pl >= NPL) return NULL;
        int c = b0start[pl + 1] - b0start[pl];
        if (c >= 5) { T->path[0] = pl; rec(T, 1, b0list + b0start[pl], c); }
    }
}

static void cells_check(long long *sets, long long *bad, int first[5]) {
    NV = q * q * q + q * q + q + 1;
    NA = malloc(sizeof *NA * NV);
    int nvc = 0;
    for (int a0 = 0; a0 < 2; a0++)
        for (int a1 = 0; a1 < q; a1++)
            for (int a2 = 0; a2 < q; a2++)
                for (int a3 = 0; a3 < q; a3++) {
                    int lead = a0 ? 1 : a1 ? a1 : a2 ? a2 : a3;  /* first nonzero coordinate must be 1 */
                    if (lead != 1) continue;
                    NA[nvc][0] = (uint8_t)a0; NA[nvc][1] = (uint8_t)a1; NA[nvc][2] = (uint8_t)a2; NA[nvc][3] = (uint8_t)a3; nvc++;
                }
    if (nvc != NV) { fprintf(stderr, "wrong number of hyperplane normals\n"); exit(2); }
    NPL = NV * q;
    double c5 = (double)k * (k - 1) * (k - 2) * (k - 3) * (k - 4) / 120, bestcost = 1e300;
    for (int mm = 1; mm < n; mm++) {  /* bucket entries (about k NV^m) plus sets at depth m (about C(k,5) / q^m) */
        double cost = (double)k * pow_int(NV, mm) + 3 * c5 / pow_int(q, mm);
        if (cost < bestcost) { bestcost = cost; M = mm; }
    }
    if (getenv("CHECK_M")) M = atoi(getenv("CHECK_M"));  /* depth override, for testing the bucketing */
    if (M < 1) M = 1;
    if (M > n - 1) M = n - 1;
    b0start = calloc(NPL + 1, sizeof(int));
    b0list = malloc(sizeof(int) * (size_t)k * NV);
    for (int c = 0; c < k; c++) for (int i = 0; i < NV; i++) b0start[plane_of(i, 0, c) + 1]++;
    for (int pl = 0; pl < NPL; pl++) b0start[pl + 1] += b0start[pl];
    int *fill = malloc(sizeof(int) * NPL), maxb = 0;
    memcpy(fill, b0start, sizeof(int) * NPL);
    for (int c = 0; c < k; c++) for (int i = 0; i < NV; i++) b0list[fill[plane_of(i, 0, c)]++] = c;
    for (int pl = 0; pl < NPL; pl++) if (b0start[pl + 1] - b0start[pl] > maxb) maxb = b0start[pl + 1] - b0start[pl];
    int nth = (int)sysconf(_SC_NPROCESSORS_ONLN);
    if (getenv("CHECK_THREADS")) nth = atoi(getenv("CHECK_THREADS"));
    if (nth < 1) nth = 1;
    if (nth > 64) nth = 64;
    TL = calloc(nth, sizeof(struct tl));
    pthread_t th[64];
    for (int w = 0; w < nth; w++) {
        for (int lev = 1; lev < M; lev++) {
            TL[w].pid[lev] = malloc(sizeof(int) * (size_t)maxb * NV);
            TL[w].ent[lev] = malloc(sizeof(int) * (size_t)maxb * NV);
            TL[w].cnt[lev] = calloc(NPL, sizeof(int));
            TL[w].off[lev] = malloc(sizeof(int) * NPL);
            TL[w].touched[lev] = malloc(sizeof(int) * NPL);
        }
        TL[w].dv = malloc(sizeof(int[4]) * (size_t)(maxb + 1));
        pthread_create(&th[w], NULL, worker, &TL[w]);
    }
    *sets = *bad = 0;
    first[0] = -1;
    for (int w = 0; w < nth; w++) {
        pthread_join(th[w], NULL);
        *sets += TL[w].sets;
        if (TL[w].bad && first[0] < 0) memcpy(first, TL[w].first, sizeof(int) * 5);
        *bad += TL[w].bad;
    }
    printf("cells method: %d rows bucketed by hyperplanes, %d threads\n", M, nth);
}

/* hybrid cyclic method (see the header) */
static int ncyc, crow[MAXN], noth, orow[MAXN];  /* rows that are affine progressions, and the others */

static int affine_shift(int r) {  /* 1 if row r is v, Tv, T^2 v, ... for an invertible affine map T of AG(4,q): in
                                     coordinates (1, x, y, z, w), a 5 x 5 matrix T with T h_j = h_(j+1) for every j */
    for (int j0 = 0; j0 + 5 < k && j0 < 64; j0++) {
        int aug[5][10];  /* [V^T | W^T], V = h_j0..h_(j0+4) as columns, W = h_(j0+1)..h_(j0+5): T V = W */
        for (int i = 0; i < 5; i++) {
            int a = j0 + i, b = a + 1;
            int hv[5] = {1, X[r][a], Y[r][a], Z[r][a], W[r][a]}, hw[5] = {1, X[r][b], Y[r][b], Z[r][b], W[r][b]};
            for (int j = 0; j < 5; j++) { aug[i][j] = hv[j]; aug[i][5 + j] = hw[j]; }
        }
        int sing = 0;
        for (int c = 0; c < 5 && !sing; c++) {  /* Gauss-Jordan on the left block */
            int piv = -1;
            for (int i = c; i < 5 && piv < 0; i++) if (aug[i][c]) piv = i;
            if (piv < 0) { sing = 1; break; }
            for (int j = 0; j < 10; j++) { int t = aug[c][j]; aug[c][j] = aug[piv][j]; aug[piv][j] = t; }
            int iv = 0;
            for (int x = 1; x < q; x++) if (MUL[aug[c][c]][x] == 1) iv = x;
            for (int j = 0; j < 10; j++) aug[c][j] = MUL[aug[c][j]][iv];
            for (int i = 0; i < 5; i++)
                if (i != c && aug[i][c]) { int f = aug[i][c]; for (int j = 0; j < 10; j++) aug[i][j] = SUB[aug[i][j]][MUL[f][aug[c][j]]]; }
        }
        if (sing) continue;  /* these five points lie on a hyperplane: try the next window */
        int Tt[5][5], E[5][5], rank = 0;  /* right block is T^T */
        for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) Tt[i][j] = E[i][j] = aug[i][5 + j];
        for (int c = 0; c < 5; c++) {  /* T invertible: rank 5 */
            int piv = -1;
            for (int i = rank; i < 5 && piv < 0; i++) if (E[i][c]) piv = i;
            if (piv < 0) continue;
            for (int j = 0; j < 5; j++) { int t = E[rank][j]; E[rank][j] = E[piv][j]; E[piv][j] = t; }
            int iv = 0;
            for (int x = 1; x < q; x++) if (MUL[E[rank][c]][x] == 1) iv = x;
            for (int i = rank + 1; i < 5; i++)
                if (E[i][c]) { int f = MUL[E[i][c]][iv]; for (int j = 0; j < 5; j++) E[i][j] = SUB[E[i][j]][MUL[f][E[rank][j]]]; }
            rank++;
        }
        if (rank < 5) return 0;
        for (int j = 0; j + 1 < k; j++) {  /* (T h)_i = sum_l Tt[l][i] h_l */
            int h[5] = {1, X[r][j], Y[r][j], Z[r][j], W[r][j]}, g[5] = {1, X[r][j + 1], Y[r][j + 1], Z[r][j + 1], W[r][j + 1]};
            for (int i = 0; i < 5; i++) {
                int v = 0;
                for (int l = 0; l < 5; l++) v = ADD[v][MUL[Tt[l][i]][h[l]]];
                if (v != g[i]) return 0;
            }
        }
        return 1;
    }
    return 0;
}

static inline int through0(int i, int r, int c) {  /* column c's point on the hyperplane with normal i through column 0's */
    int u[4];
    diff(r, 0, c, u);
    return ADD[ADD[MUL[NA[i][0]][u[0]]][MUL[NA[i][1]][u[1]]]][ADD[MUL[NA[i][2]][u[2]]][MUL[NA[i][3]][u[3]]]] == 0;
}

static int canonical0(const struct tl *T, const int *s) {  /* s: the four columns besides column 0 */
    for (int m = 0; m < M; m++) {
        int best = -1;
        for (int i = 0; i < NV && best < 0; i++) {
            int all = 1;
            for (int j = 0; j < 4 && all; j++) all = through0(i, crow[m], s[j]);
            if (all) best = i;
        }
        if (best != T->path[m]) return 0;
    }
    return 1;
}

static void leaf0(struct tl *T, const int *L, int len) {  /* sets {0} + four of L: on one hyperplane in cyclic rows
                                                              crow[M..], then every shift in the other rows */
    int (*dv)[4] = T->dv, r0 = M < ncyc ? crow[M] : -1;
    if (r0 >= 0) for (int j = 0; j < len; j++) diff(r0, 0, L[j], dv[j]);
    for (int x = 0; x < len; x++)
        for (int y = x + 1; y < len; y++)
            for (int z = y + 1; z < len; z++) {
                int N[4];
                if (r0 >= 0) cofactors(dv[x], dv[y], dv[z], N);
                for (int t = z + 1; t < len; t++) {
                    int s[4] = {L[x], L[y], L[z], L[t]};
                    int ok = r0 >= 0 && dot4(N, dv[t]) != 0;
                    for (int m = M + 1; m < ncyc && !ok; m++) ok = indep(crow[m], 0, s[0], s[1], s[2], s[3]);
                    T->sets++;
                    if (ok || !canonical0(T, s)) continue;
                    T->base++;  /* fails in every cyclic row: so does each shift; test the shifts in the other rows */
                    for (int sh = 0; sh + s[3] < k; sh++) {
                        int c = 0;
                        for (int o = 0; o < noth && !c; o++) c = indep(orow[o], sh, sh + s[0], sh + s[1], sh + s[2], sh + s[3]);
                        T->shifted++;
                        if (!c) {
                            if (!T->bad) { T->first[0] = sh; for (int j = 0; j < 4; j++) T->first[j + 1] = sh + s[j]; }
                            T->bad++;
                        }
                    }
                }
            }
}

static void rec0(struct tl *T, int lev, const int *L, int len) {  /* buckets by normal in cyclic row crow[lev] */
    if (lev == M) { leaf0(T, L, len); return; }
    int r = crow[lev], *pid = T->pid[lev], *ent = T->ent[lev], *cnt = T->cnt[lev], *off = T->off[lev], *touched = T->touched[lev];
    int nt = 0, e = 0;
    for (int x = 0; x < len; x++) {
        int e0 = e, u[4];
        for (int i = 0; i < NV; i++)
            if (through0(i, r, L[x])) {
                pid[e++] = i;
                if (cnt[i]++ == 0) touched[nt++] = i;
            }
        diff(r, 0, L[x], u);  /* a point other than column 0's lies on q^2 + q + 1 of its hyperplanes */
        if (e - e0 != (!u[0] && !u[1] && !u[2] && !u[3] ? NV : q * q + q + 1)) { fprintf(stderr, "incidence count is wrong\n"); exit(2); }
    }
    int st = 0;
    for (int t = 0; t < nt; t++) { off[touched[t]] = st; st += cnt[touched[t]]; }
    e = 0;
    for (int x = 0; x < len; x++) {
        int u[4];
        diff(r, 0, L[x], u);
        int on = !u[0] && !u[1] && !u[2] && !u[3] ? NV : q * q + q + 1;  /* entries this column made */
        for (int j = 0; j < on; j++) ent[off[pid[e++]]++] = L[x];
    }
    for (int t = 0; t < nt; t++) {
        int i = touched[t], c = cnt[i];
        if (c >= 4) { T->path[lev] = i; rec0(T, lev + 1, ent + off[i] - c, c); }
    }
    for (int t = 0; t < nt; t++) cnt[touched[t]] = 0;
}

static int *c0start, *c0list, nextnormal;

static void *worker0(void *arg) {
    struct tl *T = arg;
    for (;;) {
        int i = __sync_fetch_and_add(&nextnormal, 1);
        if (i >= NV) return NULL;
        if (PDONE && PDONE[i]) continue;  /* finished by an earlier run (CHECK_PROGRESS) */
        int c = c0start[i + 1] - c0start[i];
        long long s0 = T->sets, b0 = T->bad, a0 = T->base, h0 = T->shifted;
        if (c >= 4) { T->path[0] = i; rec0(T, 1, c0list + c0start[i], c); }
        progress_line(i, T->sets - s0, T->bad - b0, T->base - a0, T->shifted - h0, !b0 && T->bad ? T->first : NULL, 5);
    }
}

static void make_normals(void) {
    NV = q * q * q + q * q + q + 1;
    NA = malloc(sizeof *NA * NV);
    int nvc = 0;
    for (int a0 = 0; a0 < 2; a0++)
        for (int a1 = 0; a1 < q; a1++)
            for (int a2 = 0; a2 < q; a2++)
                for (int a3 = 0; a3 < q; a3++) {
                    int lead = a0 ? 1 : a1 ? a1 : a2 ? a2 : a3;  /* first nonzero coordinate must be 1 */
                    if (lead != 1) continue;
                    NA[nvc][0] = (uint8_t)a0; NA[nvc][1] = (uint8_t)a1; NA[nvc][2] = (uint8_t)a2; NA[nvc][3] = (uint8_t)a3; nvc++;
                }
    if (nvc != NV) { fprintf(stderr, "wrong number of hyperplane normals\n"); exit(2); }
}

static void cyclic_check(long long *sets, long long *bad, int first[5]) {
    make_normals();
    int NP = q * q + q + 1;  /* hyperplanes through two distinct points */
    double c4 = (double)(k - 1) * (k - 2) * (k - 3) * (k - 4) / 24, bestcost = 1e300;
    for (int mm = 1; mm <= ncyc; mm++) {  /* bucket entries (about k NP^m) plus sets at depth m (about C(k-1,4) / q^m) */
        double cost = (double)k * pow_int(NP, mm) + 3 * c4 / pow_int(q, mm);
        if (cost < bestcost) { bestcost = cost; M = mm; }
    }
    if (getenv("CHECK_M")) M = atoi(getenv("CHECK_M"));
    if (M < 1) M = 1;
    if (M > ncyc) M = ncyc;
    c0start = calloc(NV + 1, sizeof(int));
    for (int c = 1; c < k; c++) for (int i = 0; i < NV; i++) if (through0(i, crow[0], c)) c0start[i + 1]++;
    for (int i = 0; i < NV; i++) c0start[i + 1] += c0start[i];
    c0list = malloc(sizeof(int) * (size_t)(c0start[NV] + 1));
    int *fill = malloc(sizeof(int) * NV), maxb = 0;
    memcpy(fill, c0start, sizeof(int) * NV);
    for (int c = 1; c < k; c++) for (int i = 0; i < NV; i++) if (through0(i, crow[0], c)) c0list[fill[i]++] = c;
    for (int i = 0; i < NV; i++) if (c0start[i + 1] - c0start[i] > maxb) maxb = c0start[i + 1] - c0start[i];
    int nth = (int)sysconf(_SC_NPROCESSORS_ONLN);
    if (getenv("CHECK_THREADS")) nth = atoi(getenv("CHECK_THREADS"));
    if (nth < 1) nth = 1;
    if (nth > 64) nth = 64;
    progress_open(ARRAY, 5, q, M, NV, 5);
    TL = calloc(nth, sizeof(struct tl));
    pthread_t th[64];
    for (int w = 0; w < nth; w++) {
        for (int lev = 1; lev < M; lev++) {
            TL[w].pid[lev] = malloc(sizeof(int) * (size_t)maxb * NV);
            TL[w].ent[lev] = malloc(sizeof(int) * (size_t)maxb * NV);
            TL[w].cnt[lev] = calloc(NV, sizeof(int));
            TL[w].off[lev] = malloc(sizeof(int) * NV);
            TL[w].touched[lev] = malloc(sizeof(int) * NV);
        }
        TL[w].dv = malloc(sizeof(int[4]) * (size_t)(maxb + 1));
        pthread_create(&th[w], NULL, worker0, &TL[w]);
    }
    *sets = *bad = 0;
    long long base = 0, shifted = 0;
    first[0] = -1;
    for (int w = 0; w < nth; w++) {
        pthread_join(th[w], NULL);
        *sets += TL[w].sets; base += TL[w].base; shifted += TL[w].shifted;
        if (TL[w].bad && first[0] < 0) memcpy(first, TL[w].first, sizeof(int) * 5);
        *bad += TL[w].bad;
    }
    *sets += PSETS; *bad += PBAD; base += PBASE; shifted += PSHIFT;
    if (PBAD && first[0] < 0) memcpy(first, PFIRST, sizeof(int) * 5);
    if (PRESUMED) printf("resumed: %d of %d normals were finished by an earlier run (CHECK_PROGRESS) and their tallies added\n", PRESUMED, NV);
    printf("hybrid cyclic method: %d rows are affine progressions v, Tv, T^2 v, ... (T invertible), so a set of five columns "
           "fails in all of them exactly when its shift to column 0 does; %d of them bucketed by hyperplanes through column "
           "0's point, %d threads; %lld sets holding column 0 fail in every such row, and their %lld shifts were tested in "
           "the other %d rows\n", ncyc, M, nth, base, shifted, noth);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: scphf5_check q FILE [SAMPLES] [brute|cells]\n"); return 2; }
    q = atoi(argv[1]);
    if (q < 2 || q > MAXQ || !setup()) { fprintf(stderr, "q is not a supported field order\n"); return 2; }
    ARRAY = argv[2];
    FILE *f = fopen(argv[2], "r");
    if (!f) { perror(argv[2]); return 2; }
    static char line[1 << 23];
    int Q4 = q * q * q * q;
    k = -1;
    while (fgets(line, sizeof line, f)) {
        if (line[0] < '0' || line[0] > '9') continue;
        if (n == MAXN) { fprintf(stderr, "too many rows\n"); return 2; }
        int c = 0;
        X[n] = malloc(MAXK); Y[n] = malloc(MAXK); Z[n] = malloc(MAXK); W[n] = malloc(MAXK);
        for (char *s = strtok(line, " \t\n"); s; s = strtok(NULL, " \t\n")) {
            long id = atol(s);
            if (id < 0 || id >= Q4 || c == MAXK) { fprintf(stderr, "bad point id or too many columns\n"); return 2; }
            X[n][c] = (uint8_t)(id / (q * q * q)); Y[n][c] = (uint8_t)(id / (q * q) % q);
            Z[n][c] = (uint8_t)(id / q % q); W[n][c] = (uint8_t)(id % q); c++;
        }
        if (k >= 0 && c != k) { fprintf(stderr, "rows differ in length\n"); return 2; }
        k = c; n++;
    }
    fclose(f);
    if (n < 2 || k < 5) { fprintf(stderr, "no array\n"); return 2; }
    /* 1. geometry, every set of five columns */
    long long sets = 0, bad = 0;
    int fs[5] = {-1, -1, -1, -1, -1};
    double c5 = (double)k * (k - 1) * (k - 2) * (k - 3) * (k - 4) / 120;
    for (int r = 0; r < n; r++) { if (affine_shift(r)) crow[ncyc++] = r; else orow[noth++] = r; }
    int cyclic = ncyc >= 1;
    const char *method = argc > 4 ? argv[4] : c5 <= 1e10 ? "brute" : cyclic ? "cyclic" : "cells";
    if (!strcmp(method, "cyclic") && !cyclic) { fprintf(stderr, "no row is an affine progression\n"); return 2; }
    if (!strcmp(method, "cyclic")) cyclic_check(&sets, &bad, fs);
    else if (!strcmp(method, "cells")) cells_check(&sets, &bad, fs);
    else if (strcmp(method, "brute")) { fprintf(stderr, "method is brute, cells or cyclic\n"); return 2; }
    else {
        int (*N)[4] = malloc(sizeof(int[4]) * n);
        for (int a = 0; a < k; a++)
            for (int b = a + 1; b < k; b++)
                for (int c = b + 1; c < k; c++)
                    for (int d = c + 1; d < k; d++) {
                        for (int r = 0; r < n; r++) {
                            int u[4], v[4], w[4];
                            diff(r, a, b, u); diff(r, a, c, v); diff(r, a, d, w);
                            cofactors(u, v, w, N[r]);
                        }
                        for (int e = d + 1; e < k; e++) {
                            int ok = 0;
                            for (int r = 0; r < n && !ok; r++) { int x[4]; diff(r, a, e, x); ok = dot4(N[r], x) != 0; }
                            sets++;
                            if (!ok) { if (!bad) { fs[0] = a; fs[1] = b; fs[2] = c; fs[3] = d; fs[4] = e; } bad++; }
                        }
                    }
    }
    printf("SCPHF(%d; %d, %d^4, 5): %lld sets of five columns %s, %lld always on one hyperplane", n, k, q, sets,
           !strcmp(method, "brute") ? "checked" : !strcmp(method, "cells") ? "tested (the rest leave one hyperplane in a bucketed row)"
           : "holding column 0 tested (the rest leave one hyperplane in a bucketed cyclic row)", bad);
    if (bad) printf(" (first: columns %d, %d, %d, %d, %d)", fs[0], fs[1], fs[2], fs[3], fs[4]);
    printf("\n");
    /* 2. covering-array spot check */
    long N = (long)n * (Q4 * q - q) + q, missing = 0;
    int Q5 = Q4 * q;
    double per = 5.0 * n * Q5;
    long samples = argc > 3 ? atol(argv[3]) : (long)(2e9 / per);
    if (argc <= 3) samples = samples < 20 ? 20 : samples > 500 ? 500 : samples;
    uint32_t *stamp = calloc(Q5, sizeof(uint32_t));
    uint64_t s = 0x2545F4914F6CDD1DULL;
    for (long t = 1; t <= samples; t++) {
        int col[5];
        for (;;) {
            for (int i = 0; i < 5; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; col[i] = (int)(s % (uint64_t)k); }
            int dup = 0;
            for (int i = 0; i < 5; i++) for (int j = i + 1; j < 5; j++) dup |= col[i] == col[j];
            if (!dup) break;
        }
        int seen = 0;
        for (int r = 0; r < n; r++)
            for (int u1 = 0; u1 < q; u1++)
                for (int u2 = 0; u2 < q; u2++)
                    for (int u3 = 0; u3 < q; u3++)
                        for (int u4 = 0; u4 < q; u4++) {
                            if (!u1 && !u2 && !u3 && !u4 && r > 0) continue;  /* constant rows once */
                            int base[5];
                            for (int i = 0; i < 5; i++)
                                base[i] = ADD[ADD[MUL[u1][X[r][col[i]]]][MUL[u2][Y[r][col[i]]]]][ADD[MUL[u3][Z[r][col[i]]]][MUL[u4][W[r][col[i]]]]];
                            for (int u0 = 0; u0 < q; u0++) {
                                int code = (((ADD[u0][base[0]] * q + ADD[u0][base[1]]) * q + ADD[u0][base[2]]) * q + ADD[u0][base[3]]) * q + ADD[u0][base[4]];
                                if (stamp[code] != (uint32_t)t) { stamp[code] = (uint32_t)t; seen++; }
                            }
                        }
        if (seen != Q5) missing++;
    }
    printf("CA(%ld; 5, %d, %d): %ld random sets of five columns, %ld missing a tuple\n", N, k, q, samples, missing);
    printf("%s\n", bad || missing ? "FAIL" : "PASS");
    return bad || missing ? 1 : 0;
}
