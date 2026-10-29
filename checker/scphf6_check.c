/* Independent check of a strength-6 Sherwood CPHF (engine/native/cphf6c.c output). Field arithmetic as in
   independent/scphf5_check.c (Horner multiplication modulo the listed polynomial, field axioms tested before use),
   written apart from the search; points of AG(5,q) as ids (((x0 q + x1) q + x2) q + x3) q + x4. Ranks and null
   vectors by Gaussian elimination (the search uses exterior products).
   1. Every six columns must hold, in some row, six points not on one hyperplane (the five differences from the
      first point have rank 5). Two exact methods:
      "brute" tries all C(k,6) sets.
      "cyclic" (hybrid) uses the rows that are affine progressions v, Tv, T^2 v, ... for an invertible affine map T
      of AG(5,q) (T solved from six consecutive points of the row in coordinates (1, x0, ..., x4), then checked on
      every point). T^s maps columns j, j', ... of such a row to j + s, j' + s, ... and keeps points on or off a
      hyperplane, so a set of six columns fails in all of these rows exactly when its shift by minus its first
      column does. The sets holding column 0 that fail in all of them are found by bucketing the other columns by
      every hyperplane through column 0's point and theirs, row by row (a set lies on one hyperplane with column 0 in
      each of those rows exactly when it shares a bucket), the sets sharing a bucket at depth M are tested in the
      remaining such rows, and each failing set is counted once, in the bucket path of the smallest hyperplanes
      holding it; then every shift of each is tested in the other rows. Any failing set of the array is such a
      shift, so none is missed.
      Default: brute when C(k,6) <= 1e10, else cyclic (METHOD forces one; threads from CHECK_THREADS, depth from
      CHECK_M).
   2. Spot check of the covering array it gives, CA(n(q^6 - q) + q; 6, k, q) (row (u0,..,u5) of block r puts
      u0 + u1 x0 + ... + u5 x4 in a column whose point in row r is (x0, ..., x4); the q constant rows once): for
      SAMPLES random sets of six columns (default about 2e9 symbol evaluations' worth, 1 to 100), every one of the
      q^6 tuples of symbols must appear.
   cc -O3 -o scphf6_check scphf6_check.c -lpthread && ./scphf6_check q FILE [SAMPLES] [brute|cyclic] */
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
#define MAXK 10000

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

static int n, k, INV[MAXQ];
static uint8_t *Xc[MAXN][5];       /* coordinate c of column j's point in row r: Xc[r][c][j] */

static inline void diff(int r, int a, int b, int *u) { for (int c = 0; c < 5; c++) u[c] = SUB[Xc[r][c][b]][Xc[r][c][a]]; }

static int rank_of(int rows, int (*m)[5]) {  /* rank of rows x 5 matrix (destroyed) */
    int rank = 0;
    for (int c = 0; c < 5 && rank < rows; c++) {
        int piv = -1;
        for (int i = rank; i < rows && piv < 0; i++) if (m[i][c]) piv = i;
        if (piv < 0) continue;
        for (int j = 0; j < 5; j++) { int t = m[rank][j]; m[rank][j] = m[piv][j]; m[piv][j] = t; }
        int iv = INV[m[rank][c]];
        for (int i = rank + 1; i < rows; i++)
            if (m[i][c]) { int f = MUL[m[i][c]][iv]; for (int j = 0; j < 5; j++) m[i][j] = SUB[m[i][j]][MUL[f][m[rank][j]]]; }
        rank++;
    }
    return rank;
}

static int indep(int r, const int *s) {  /* columns s[0..5] independent in row r: rank of differences is 5 */
    int m[5][5];
    for (int i = 0; i < 5; i++) diff(r, s[0], s[i + 1], m[i]);
    return rank_of(5, m) == 5;
}

/* hyperplane normals: classes of PG(4,q), last nonzero coordinate 1 (the search uses the first) */
static int NV, M;
static int (*NA)[5];
static int *pw5;                   /* q^i */

static int nclass(const int *h) {  /* index of the class of a nonzero vector */
    int l = 4;
    while (!h[l]) l--;
    int s = INV[h[l]], idx = 0;
    for (int j = 0; j < l; j++) idx = idx * q + MUL[h[j]][s];
    int base = 0;
    for (int j = 0; j < l; j++) base += pw5[j];  /* classes with last nonzero at j come first: q^j of them */
    return base + idx;
}

static void make_normals(void) {
    pw5 = malloc(sizeof(int) * 6);
    pw5[0] = 1;
    for (int i = 1; i < 6; i++) pw5[i] = pw5[i - 1] * q;
    NV = (pw5[5] - 1) / (q - 1);
    NA = malloc(sizeof *NA * NV);
    char *seen = calloc(NV, 1);
    for (int l = 0; l < 5; l++)
        for (int t = 0; t < pw5[l]; t++) {
            int h[5] = {0, 0, 0, 0, 0}, v = t;
            h[l] = 1;
            for (int j = l - 1; j >= 0; j--) { h[j] = v % q; v /= q; }
            int id = nclass(h);
            if (id < 0 || id >= NV || seen[id]) { fprintf(stderr, "normal numbering is wrong\n"); exit(2); }
            seen[id] = 1;
            memcpy(NA[id], h, sizeof h);
        }
    free(seen);
}

static int through(const int *u, int *out) {  /* every normal class h with h . u = 0 (u != 0); returns the count */
    int l = 4;
    while (!u[l]) l--;  /* solve on the last nonzero coordinate of u */
    int s = INV[u[l]], cnt = 0, fr[4], nf = 0;
    for (int j = 0; j < 5; j++) if (j != l) fr[nf++] = j;
    for (int lead = 3; lead >= 0; lead--)  /* free part g on fr, last nonzero coordinate 1 */
        for (int t = 0; t < pw5[lead]; t++) {
            int g[4] = {0, 0, 0, 0}, v = t, h[5];
            g[lead] = 1;
            for (int j = lead - 1; j >= 0; j--) { g[j] = v % q; v /= q; }
            int acc = 0;
            for (int j = 0; j < 4; j++) { h[fr[j]] = g[j]; acc = ADD[acc][MUL[g[j]][u[fr[j]]]]; }
            h[l] = SUB[0][MUL[acc][s]];
            out[cnt++] = nclass(h);
        }
    return cnt;
}

/* hybrid cyclic method */
static int ncyc, crow[MAXN], noth, orow[MAXN];

static int affine_shift(int r) {  /* row r is v, Tv, T^2 v, ... for an invertible affine T: a 6 x 6 matrix on (1, x) */
    for (int j0 = 0; j0 + 6 < k && j0 < 64; j0++) {
        int aug[6][12];
        for (int i = 0; i < 6; i++) {
            int a = j0 + i, b = a + 1;
            aug[i][0] = 1; aug[i][6] = 1;
            for (int c = 0; c < 5; c++) { aug[i][1 + c] = Xc[r][c][a]; aug[i][7 + c] = Xc[r][c][b]; }
        }
        int sing = 0;
        for (int c = 0; c < 6 && !sing; c++) {
            int piv = -1;
            for (int i = c; i < 6 && piv < 0; i++) if (aug[i][c]) piv = i;
            if (piv < 0) { sing = 1; break; }
            for (int j = 0; j < 12; j++) { int t = aug[c][j]; aug[c][j] = aug[piv][j]; aug[piv][j] = t; }
            int iv = INV[aug[c][c]];
            for (int j = 0; j < 12; j++) aug[c][j] = MUL[aug[c][j]][iv];
            for (int i = 0; i < 6; i++)
                if (i != c && aug[i][c]) { int f = aug[i][c]; for (int j = 0; j < 12; j++) aug[i][j] = SUB[aug[i][j]][MUL[f][aug[c][j]]]; }
        }
        if (sing) continue;
        int Tt[6][6], E[6][6], rank = 0;  /* right block is T^T */
        for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) Tt[i][j] = E[i][j] = aug[i][6 + j];
        for (int c = 0; c < 6; c++) {
            int piv = -1;
            for (int i = rank; i < 6 && piv < 0; i++) if (E[i][c]) piv = i;
            if (piv < 0) continue;
            for (int j = 0; j < 6; j++) { int t = E[rank][j]; E[rank][j] = E[piv][j]; E[piv][j] = t; }
            int iv = INV[E[rank][c]];
            for (int i = rank + 1; i < 6; i++)
                if (E[i][c]) { int f = MUL[E[i][c]][iv]; for (int j = 0; j < 6; j++) E[i][j] = SUB[E[i][j]][MUL[f][E[rank][j]]]; }
            rank++;
        }
        if (rank < 6) return 0;
        for (int j = 0; j + 1 < k; j++) {
            int h[6] = {1, Xc[r][0][j], Xc[r][1][j], Xc[r][2][j], Xc[r][3][j], Xc[r][4][j]};
            int g[6] = {1, Xc[r][0][j + 1], Xc[r][1][j + 1], Xc[r][2][j + 1], Xc[r][3][j + 1], Xc[r][4][j + 1]};
            for (int i = 0; i < 6; i++) {
                int v = 0;
                for (int l = 0; l < 6; l++) v = ADD[v][MUL[Tt[l][i]][h[l]]];
                if (v != g[i]) return 0;
            }
        }
        return 1;
    }
    return 0;
}

static int *PLc[MAXN], *PLn[MAXN];  /* bucketed cyclic row m: the normals through column c and column 0 (PLn[m][c] of them) */

struct tl {
    int *pid[MAXN], *ent[MAXN], *cnt[MAXN], *off[MAXN], *touched[MAXN], *npc[MAXN];
    int path[MAXN];
    int (*dv)[5], (*r1)[5], (*r2)[5], *cls;
    long long sets, bad, base, shifted;
    int first[6];
};

static int canonical0(const struct tl *T, const int *s) {  /* smallest normal through column 0 and the five, per row */
    for (int m = 0; m < M; m++) {
        int r = crow[m], mat[5][5];
        for (int i = 0; i < 5; i++) diff(r, 0, s[i], mat[i]);
        int best = INT_MAX;
        for (int i = 0; i < NV; i++) {  /* only on a failing set: a full scan is fine */
            int on = 1;
            for (int j = 0; j < 5 && on; j++) {
                int v = 0;
                for (int c = 0; c < 5; c++) v = ADD[v][MUL[NA[i][c]][mat[j][c]]];
                on = v == 0;
            }
            if (on) { best = i; break; }
        }
        if (best != T->path[m]) return 0;
    }
    return 1;
}

static uint8_t (*DV[MAXN])[5];  /* DV[m][c]: column c's point minus column 0's in cyclic row crow[m], m >= M (made once) */

static int still_dep(const int *s5, int from) {  /* columns s5[0..4] stay on one hyperplane with column 0 in every cyclic
                                                    row crow[m], m >= from */
    for (int m = from; m < ncyc; m++) {
        int mat[5][5];
        for (int i = 0; i < 5; i++) for (int c = 0; c < 5; c++) mat[i][c] = DV[m][s5[i]][c];
        if (rank_of(5, mat) == 5) return 0;
    }
    return 1;
}

static void found(struct tl *T, const int *s) {  /* {0, s[1..5]} fails in every cyclic row: count it once (canonical
                                                    bucket path), then test each shift in the other rows */
    if (!canonical0(T, s + 1)) return;
    T->base++;
    for (int sh = 0; sh + s[5] < k; sh++) {
        int t6[6], c2 = 0;
        for (int x = 0; x < 6; x++) t6[x] = sh + s[x];
        for (int o = 0; o < noth && !c2; o++) c2 = indep(orow[o], t6);
        T->shifted++;
        if (!c2) { if (!T->bad) memcpy(T->first, t6, sizeof t6); T->bad++; }
    }
}

static void rest_dep(struct tl *T, int *s, const int *L, int from, int len, int need) {  /* row crow[M] already
    fails for every completion: fill s[6 - need..5] from L[from..] and test the later cyclic rows */
    if (!need) { T->sets++; if (still_dep(s + 1, M + 1)) found(T, s); return; }
    for (int x = from; x + need <= len; x++) { s[6 - need] = L[x]; rest_dep(T, s, L, x + 1, len, need - 1); }
}

static int reduce(const int *u, int *n) {  /* pivot = first nonzero coordinate of u, n = u scaled to 1 there; -1 if u = 0 */
    int pv = -1;
    for (int x = 0; x < 5 && pv < 0; x++) if (u[x]) pv = x;
    if (pv < 0) return -1;
    int iv = INV[u[pv]];
    for (int x = 0; x < 5; x++) n[x] = MUL[u[x]][iv];
    return pv;
}

static void leaf0(struct tl *T, const int *L, int len) {  /* six-sets {0} + five of L. In row crow[M] the directions from
    column 0's point are reduced modulo those of the first three chosen columns; five are dependent exactly when the
    last two reduced vectors (two coordinates left) are proportional or one is zero, i.e. share a class of PG(1,q). */
    if (M >= ncyc) {  /* every cyclic row is bucketed: each five of L fails in all of them */
        int s[6] = {0};
        for (int a = 0; a + 4 < len; a++) for (int b = a + 1; b + 3 < len; b++) for (int c = b + 1; c + 2 < len; c++)
            for (int d = c + 1; d + 1 < len; d++) for (int e = d + 1; e < len; e++) {
                s[1] = L[a]; s[2] = L[b]; s[3] = L[c]; s[4] = L[d]; s[5] = L[e];
                T->sets++;
                found(T, s);
            }
        return;
    }
    uint8_t (*D)[5] = DV[M];
    int (*r1)[5] = T->r1, (*r2)[5] = T->r2, *cls = T->cls, s[6] = {0};
    for (int a = 0; a + 4 < len; a++) {
        int u[5], na[5], pa;
        for (int x = 0; x < 5; x++) u[x] = D[L[a]][x];
        s[1] = L[a];
        if ((pa = reduce(u, na)) < 0) { rest_dep(T, s, L, a + 1, len, 4); continue; }  /* on column 0's point */
        for (int x = a + 1; x < len; x++) { int f = D[L[x]][pa]; for (int y = 0; y < 5; y++) r1[x][y] = SUB[D[L[x]][y]][MUL[f][na[y]]]; }
        for (int b = a + 1; b + 3 < len; b++) {
            int nb[5], pb;
            s[2] = L[b];
            if ((pb = reduce(r1[b], nb)) < 0) { rest_dep(T, s, L, b + 1, len, 3); continue; }  /* on one line with 0, a */
            for (int x = b + 1; x < len; x++) { int f = r1[x][pb]; for (int y = 0; y < 5; y++) r2[x][y] = SUB[r1[x][y]][MUL[f][nb[y]]]; }
            for (int c = b + 1; c + 2 < len; c++) {
                int nc[5], pc, f0 = -1, f1 = -1;
                s[3] = L[c];
                if ((pc = reduce(r2[c], nc)) < 0) { rest_dep(T, s, L, c + 1, len, 2); continue; }  /* on one plane */
                for (int y = 0; y < 5; y++) if (y != pa && y != pb && y != pc) { if (f0 < 0) f0 = y; else f1 = y; }
                for (int x = c + 1; x < len; x++) {  /* class of the reduced vector in its two free coordinates */
                    int y0 = SUB[r2[x][f0]][MUL[r2[x][pc]][nc[f0]]], y1 = SUB[r2[x][f1]][MUL[r2[x][pc]][nc[f1]]];
                    cls[x] = y1 ? MUL[y0][INV[y1]] : y0 ? q : -1;  /* -1: in the span of a, b, c */
                }
                for (int d = c + 1; d + 1 < len; d++)
                    for (int e = d + 1; e < len; e++) {
                        T->sets++;
                        if (cls[d] != cls[e] && cls[d] >= 0 && cls[e] >= 0) continue;  /* independent in crow[M] */
                        s[4] = L[d]; s[5] = L[e];
                        if (still_dep(s + 1, M + 1)) found(T, s);
                    }
            }
        }
    }
}

static void rec0(struct tl *T, int lev, const int *L, int len) {
    if (lev == M) { leaf0(T, L, len); return; }
    int r = crow[lev], *pid = T->pid[lev], *ent = T->ent[lev], *cnt = T->cnt[lev], *off = T->off[lev], *touched = T->touched[lev], *npc = T->npc[lev];
    int nt = 0, e = 0, NP4 = (pw5[4] - 1) / (q - 1);
    (void)r;
    for (int x = 0; x < len; x++) {
        int got = PLn[lev][L[x]];
        const int *hl = got == NV ? NULL : PLc[lev] + (size_t)L[x] * NP4;
        npc[x] = got;
        for (int j = 0; j < got; j++) { int i = hl ? hl[j] : j; pid[e++] = i; if (cnt[i]++ == 0) touched[nt++] = i; }
    }
    int st = 0;  /* only buckets of five or more are filled: smaller ones hold no set of six with column 0 */
    for (int t = 0; t < nt; t++) if (cnt[touched[t]] >= 5) { off[touched[t]] = st; st += cnt[touched[t]]; }
    e = 0;
    for (int x = 0; x < len; x++) for (int j = 0; j < npc[x]; j++) { int i = pid[e++]; if (cnt[i] >= 5) ent[off[i]++] = L[x]; }
    for (int t = 0; t < nt; t++) {
        int i = touched[t], c = cnt[i];
        if (c >= 5) { T->path[lev] = i; rec0(T, lev + 1, ent + off[i] - c, c); }
    }
    for (int t = 0; t < nt; t++) cnt[touched[t]] = 0;
}

static int *c0start, *c0list, nextnormal;
static struct tl *TL;

static void *worker0(void *arg) {
    struct tl *T = arg;
    for (;;) {
        int i = __sync_fetch_and_add(&nextnormal, 1);
        if (i >= NV) return NULL;
        if (PDONE && PDONE[i]) continue;  /* finished by an earlier run (CHECK_PROGRESS) */
        int c = c0start[i + 1] - c0start[i];
        long long s0 = T->sets, b0 = T->bad, a0 = T->base, h0 = T->shifted;
        if (c >= 5) { T->path[0] = i; rec0(T, 1, c0list + c0start[i], c); }
        progress_line(i, T->sets - s0, T->bad - b0, T->base - a0, T->shifted - h0, !b0 && T->bad ? T->first : NULL, 6);
    }
}

static void cyclic_check(long long *sets, long long *bad, int first[6]) {
    int NP4 = (pw5[4] - 1) / (q - 1);  /* hyperplanes through two distinct points */
    double c5 = (double)(k - 1) * (k - 2) * (k - 3) * (k - 4) * (k - 5) / 120, bestcost = 1e300;
    for (int mm = 1; mm <= ncyc; mm++) {
        double cost = (double)k * pow_int(NP4, mm) + 3 * c5 / pow_int(q, mm);
        if (cost < bestcost) { bestcost = cost; M = mm; }
    }
    if (getenv("CHECK_M")) M = atoi(getenv("CHECK_M"));
    if (M < 1) M = 1;
    if (M > ncyc) M = ncyc;
    for (int m = 0; m < M; m++) {  /* the normals through each column's point and column 0's, per bucketed row */
        PLc[m] = malloc(sizeof(int) * (size_t)k * NP4);
        PLn[m] = malloc(sizeof(int) * (size_t)k);
        for (int c = 1; c < k; c++) {
            int u[5];
            diff(crow[m], 0, c, u);
            if (!u[0] && !u[1] && !u[2] && !u[3] && !u[4]) { PLn[m][c] = NV; continue; }  /* on column 0's point: every normal */
            PLn[m][c] = through(u, PLc[m] + (size_t)c * NP4);
            if (PLn[m][c] != NP4) { fprintf(stderr, "incidence count is wrong\n"); exit(2); }
        }
    }
    for (int m = M; m < ncyc; m++) {  /* directions from column 0's point in the other cyclic rows */
        DV[m] = malloc(sizeof *DV[m] * (size_t)k);
        for (int c = 0; c < k; c++) { int u[5]; diff(crow[m], 0, c, u); for (int x = 0; x < 5; x++) DV[m][c][x] = (uint8_t)u[x]; }
    }
    c0start = calloc(NV + 1, sizeof(int));
    for (int c = 1; c < k; c++) for (int j = 0; j < PLn[0][c]; j++) c0start[(PLn[0][c] == NV ? j : PLc[0][(size_t)c * NP4 + j]) + 1]++;
    for (int i = 0; i < NV; i++) c0start[i + 1] += c0start[i];
    c0list = malloc(sizeof(int) * (size_t)(c0start[NV] + 1));
    int *fill = malloc(sizeof(int) * NV), maxb = 0;
    memcpy(fill, c0start, sizeof(int) * NV);
    for (int c = 1; c < k; c++) for (int j = 0; j < PLn[0][c]; j++) c0list[fill[PLn[0][c] == NV ? j : PLc[0][(size_t)c * NP4 + j]]++] = c;
    for (int i = 0; i < NV; i++) if (c0start[i + 1] - c0start[i] > maxb) maxb = c0start[i + 1] - c0start[i];
    size_t most[MAXN] = {0};  /* a list at level lev holds at most maxb columns, each with PLn[lev][c] normals */
    for (int lev = 1; lev < M; lev++) for (int c = 1; c < k; c++) if ((size_t)PLn[lev][c] > most[lev]) most[lev] = PLn[lev][c];
    int nth = (int)sysconf(_SC_NPROCESSORS_ONLN);
    if (getenv("CHECK_THREADS")) nth = atoi(getenv("CHECK_THREADS"));
    if (nth < 1) nth = 1;
    if (nth > 64) nth = 64;
    progress_open(ARRAY, 6, q, M, NV, 6);
    TL = calloc(nth, sizeof(struct tl));
    pthread_t th[64];
    for (int w = 0; w < nth; w++) {
        for (int lev = 1; lev < M; lev++) {
            TL[w].pid[lev] = malloc(sizeof(int) * (size_t)maxb * most[lev]);
            TL[w].ent[lev] = malloc(sizeof(int) * (size_t)maxb * most[lev]);
            TL[w].cnt[lev] = calloc(NV, sizeof(int));
            TL[w].off[lev] = malloc(sizeof(int) * NV);
            TL[w].touched[lev] = malloc(sizeof(int) * NV);
            TL[w].npc[lev] = malloc(sizeof(int) * (size_t)(maxb + 1));
        }
        TL[w].dv = malloc(sizeof(int[5]) * (size_t)(maxb + 1));
        TL[w].r1 = malloc(sizeof(int[5]) * (size_t)(maxb + 1));
        TL[w].r2 = malloc(sizeof(int[5]) * (size_t)(maxb + 1));
        TL[w].cls = malloc(sizeof(int) * (size_t)(maxb + 1));
        pthread_create(&th[w], NULL, worker0, &TL[w]);
    }
    *sets = *bad = 0;
    long long base = 0, shifted = 0;
    first[0] = -1;
    for (int w = 0; w < nth; w++) {
        pthread_join(th[w], NULL);
        *sets += TL[w].sets; base += TL[w].base; shifted += TL[w].shifted;
        if (TL[w].bad && first[0] < 0) memcpy(first, TL[w].first, sizeof(int) * 6);
        *bad += TL[w].bad;
    }
    *sets += PSETS; *bad += PBAD; base += PBASE; shifted += PSHIFT;
    if (PBAD && first[0] < 0) memcpy(first, PFIRST, sizeof(int) * 6);
    if (PRESUMED) printf("resumed: %d of %d normals were finished by an earlier run (CHECK_PROGRESS) and their tallies added\n", PRESUMED, NV);
    printf("hybrid cyclic method: %d rows are affine progressions v, Tv, T^2 v, ... (T invertible), so a set of six columns "
           "fails in all of them exactly when its shift to column 0 does; %d of them bucketed by hyperplanes through column "
           "0's point, %d threads; %lld sets holding column 0 fail in every such row, and their %lld shifts were tested in "
           "the other %d rows\n", ncyc, M, nth, base, shifted, noth);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: scphf6_check q FILE [SAMPLES] [brute|cyclic]\n"); return 2; }
    q = atoi(argv[1]);
    if (q < 2 || q > MAXQ || !setup()) { fprintf(stderr, "q is not a supported field order\n"); return 2; }
    for (int a = 1; a < q; a++) for (int b = 1; b < q; b++) if (MUL[a][b] == 1) INV[a] = b;
    make_normals();
    ARRAY = argv[2];
    FILE *f = fopen(argv[2], "r");
    if (!f) { perror(argv[2]); return 2; }
    static char line[1 << 24];
    long Q5 = (long)pw5[5];
    k = -1;
    while (fgets(line, sizeof line, f)) {
        if (line[0] < '0' || line[0] > '9') continue;
        if (n == MAXN) { fprintf(stderr, "too many rows\n"); return 2; }
        int c = 0;
        for (int i = 0; i < 5; i++) Xc[n][i] = malloc(MAXK);
        for (char *s = strtok(line, " \t\n"); s; s = strtok(NULL, " \t\n")) {
            long id = atol(s);
            if (id < 0 || id >= Q5 || c == MAXK) { fprintf(stderr, "bad point id or too many columns\n"); return 2; }
            for (int i = 4; i >= 0; i--) { Xc[n][i][c] = (uint8_t)(id % q); id /= q; }
            c++;
        }
        if (k >= 0 && c != k) { fprintf(stderr, "rows differ in length\n"); return 2; }
        k = c; n++;
    }
    fclose(f);
    if (n < 2 || k < 6) { fprintf(stderr, "no array\n"); return 2; }
    long long sets = 0, bad = 0;
    int fs[6] = {-1, -1, -1, -1, -1, -1};
    double c6 = (double)k * (k - 1) * (k - 2) * (k - 3) * (k - 4) * (k - 5) / 720;
    for (int r = 0; r < n; r++) { if (affine_shift(r)) crow[ncyc++] = r; else orow[noth++] = r; }
    const char *method = argc > 4 ? argv[4] : c6 <= 1e10 ? "brute" : "cyclic";
    if (!strcmp(method, "cyclic")) {
        if (!ncyc) { fprintf(stderr, "no row is an affine progression\n"); return 2; }
        cyclic_check(&sets, &bad, fs);
    } else if (strcmp(method, "brute")) { fprintf(stderr, "method is brute or cyclic\n"); return 2; }
    else {
        int s[6];
        for (s[0] = 0; s[0] < k; s[0]++)
            for (s[1] = s[0] + 1; s[1] < k; s[1]++)
                for (s[2] = s[1] + 1; s[2] < k; s[2]++)
                    for (s[3] = s[2] + 1; s[3] < k; s[3]++)
                        for (s[4] = s[3] + 1; s[4] < k; s[4]++)
                            for (s[5] = s[4] + 1; s[5] < k; s[5]++) {
                                int ok = 0;
                                for (int r = 0; r < n && !ok; r++) ok = indep(r, s);
                                sets++;
                                if (!ok) { if (!bad) memcpy(fs, s, sizeof s); bad++; }
                            }
    }
    printf("SCPHF(%d; %d, %d^5, 6): %lld sets of six columns %s, %lld always on one hyperplane", n, k, q, sets,
           !strcmp(method, "brute") ? "checked" : "holding column 0 tested (the rest leave one hyperplane in a bucketed cyclic row)", bad);
    if (bad) printf(" (first: columns %d, %d, %d, %d, %d, %d)", fs[0], fs[1], fs[2], fs[3], fs[4], fs[5]);
    printf("\n");
    /* 2. covering-array spot check */
    long Q6 = Q5 * q, N = (long)n * (Q6 - q) + q, missing = 0;
    double per = 6.0 * n * Q6;
    long samples = argc > 3 ? atol(argv[3]) : (long)(2e9 / per);
    if (argc <= 3) samples = samples < 1 ? 1 : samples > 100 ? 100 : samples;
    uint64_t *bits = malloc(sizeof(uint64_t) * (size_t)((Q6 + 63) / 64));
    uint64_t sd = 0x2545F4914F6CDD1DULL;
    for (long t = 1; t <= samples; t++) {
        int col[6];
        for (;;) {
            for (int i = 0; i < 6; i++) { sd ^= sd << 13; sd ^= sd >> 7; sd ^= sd << 17; col[i] = (int)(sd % (uint64_t)k); }
            int dup = 0;
            for (int i = 0; i < 6; i++) for (int j = i + 1; j < 6; j++) dup |= col[i] == col[j];
            if (!dup) break;
        }
        memset(bits, 0, sizeof(uint64_t) * (size_t)((Q6 + 63) / 64));
        long seen = 0;
        for (int r = 0; r < n; r++)
            for (long u = 0; u < Q5; u++) {  /* (u1..u5) = digits of u */
                int ud[5];
                long v = u;
                for (int i = 4; i >= 0; i--) { ud[i] = (int)(v % q); v /= q; }
                if (!u && r > 0) continue;  /* constant rows once */
                int base[6];
                for (int i = 0; i < 6; i++) {
                    int acc = 0;
                    for (int c = 0; c < 5; c++) acc = ADD[acc][MUL[ud[c]][Xc[r][c][col[i]]]];
                    base[i] = acc;
                }
                for (int u0 = 0; u0 < q; u0++) {
                    long code = 0;
                    for (int i = 0; i < 6; i++) code = code * q + ADD[u0][base[i]];
                    if (!(bits[code >> 6] >> (code & 63) & 1)) { bits[code >> 6] |= 1ULL << (code & 63); seen++; }
                }
            }
        if (seen != Q6) missing++;
    }
    printf("CA(%ld; 6, %d, %d): %ld random sets of six columns, %ld missing a tuple\n", N, k, q, samples, missing);
    printf("%s\n", bad || missing ? "FAIL" : "PASS");
    return bad || missing ? 1 : 0;
}
