/* fullcheck3orb2.c (16 Nov 2026, evening): fullcheck3orb with MAXQ 256 (its tables are q^2), the group test visiting each
   line once, and (later that evening) a small-class path in refine that visits only the labels present.

   fullcheck3orb.c (16 Nov 2026): fullcheck3 (below; MAXQ 64) for a family given as orbits (pq_cphf3orb's output, its
   representatives in the ca-tools coding q^2 + x q + y): header lines "# orbit family: ... M1 a M2 b reps R ...",
   "# G1 r m00 m01 m10 m11" and "# G2 r ..." (row r's two matrices over GF(q), acting on (x, y) as column vectors),
   then the n rows of the R representatives. The family is F = { G1^i G2^j c : 0 <= i < M1, 0 <= j < M2 }.
   Checked here with this program's own arithmetic: every matrix has a nonzero determinant and sends the q points of
   every line (a point and one of the q + 1 directions) to q points in one direction from the first image; G1 G2 =
   G2 G1; G1^M1 = G2^M2 = I (matrix powers). Then the maps permute F and keep coverage of every triple, and every
   triple of F is the image of one that contains a representative, so only those are decided: Algorithm R from each
   representative over all k - 1 other columns (not only earlier ones). The columns are also sorted and counted
   distinct. Expansion by precomputed matrix powers (G1^i (G2^j c)).
   Usage: fullcheck3orb q FILE [THREADS] | fullcheck3orb q - selftest

   ---- the original comment ----
   fullcheck3.c: exact check of a strength-3 Sherwood CPHF given as a ca-tools certificate (Conway coding), written
   for version 4 of the Quantavane covering-array paper as a second, separately written program for the released
   SCPHF(16; 90723, 4, 3). It shares no code with the search (engine pq_cphf3big.c) or with the data repository's
   checkers (pq_scphf3_bigcheck.c, cphf_conway_check.py).

   File: lines starting with a digit are rows; an entry is the integer id of a vector (1, x, y) of F_q^3 in base q,
   id = (1 q + x) q + y, with F_q (q = p^e) coded by base-p digits modulo the Conway polynomial below.
   Method (paper, Corollary 7 and Proposition 14): for each column c, every earlier column j gets in each row the
   direction of its point seen from the point of c (one of the q + 1 lines through it), or the wildcard when the two
   points coincide; three columns i < j < c are uncovered iff the directions of i and j agree or one is a wildcard in
   every row. Algorithm R splits the earlier columns row by row; the pairs that survive every row are confirmed by a
   3 x 3 determinant in every row (computed by the expansion formula, not by elimination).
   Usage: fullcheck3 q FILE [THREADS] | fullcheck3 q - selftest */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256  /* 16 Nov evening: 128 -> 256 (uint8 coordinates; WILD 0xFF > q + 1 for q <= 253) */
#define WILD 0xFF
static int q, p, e, CP[8];
static uint8_t ADD[MAXQ][MAXQ], SUB[MAXQ][MAXQ], MUL[MAXQ][MAXQ], INV[MAXQ];
static void die(const char *m) { fprintf(stderr, "fullcheck3: %s\n", m); exit(2); }

static void field(void) {  /* Conway polynomials (monic, low degree first) */
    static const struct { int q, p, e, f[6]; } T[] = {{4, 2, 2, {1, 1, 1}}, {8, 2, 3, {1, 1, 0, 1}}, {16, 2, 4, {1, 1, 0, 0, 1}},
        {32, 2, 5, {1, 0, 1, 0, 0, 1}}, {9, 3, 2, {2, 2, 1}}, {27, 3, 3, {1, 2, 0, 1}}, {25, 5, 2, {2, 4, 1}}};
    p = 0;
    for (size_t i = 0; i < sizeof T / sizeof *T; i++) if (T[i].q == q) { p = T[i].p; e = T[i].e; memcpy(CP, T[i].f, sizeof T[i].f); }
    if (!p) { for (int d = 2; d * d <= q; d++) if (q % d == 0) die("unsupported q"); p = q; e = 1; }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int da[8], db[8], s[8], c[16] = {0}, x = a, y = b;
            for (int i = 0; i < e; i++) { da[i] = x % p; x /= p; db[i] = y % p; y /= p; }
            int sum = 0, dif = 0, pw = 1;
            for (int i = 0; i < e; i++, pw *= p) { s[i] = (da[i] + db[i]) % p; sum += s[i] * pw; dif += ((da[i] - db[i]) % p + p) % p * pw; }
            for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) c[i + j] = (c[i + j] + da[i] * db[j]) % p;
            if (e > 1)
                for (int d = 2 * e - 2; d >= e; d--) { int t = c[d]; for (int i = 0; i <= e; i++) c[d - e + i] = ((c[d - e + i] - t * CP[i]) % p + p) % p; }
            int prod = 0;
            pw = 1;
            for (int i = 0; i < e; i++, pw *= p) prod += c[i] * pw;
            ADD[a][b] = (uint8_t)sum; SUB[a][b] = (uint8_t)dif; MUL[a][b] = (uint8_t)(e == 1 ? a * b % p : prod);
        }
    for (int a = 0; a < q; a++) {  /* field axioms, exhaustively */
        int inv = -1;
        for (int b = 0; b < q; b++) {
            if (MUL[a][b] == 1) inv = b;
            if (ADD[a][b] != ADD[b][a] || MUL[a][b] != MUL[b][a] || ADD[SUB[a][b]][b] != a) die("field axiom fails");
            for (int c = 0; c < q; c++)
                if (MUL[a][ADD[b][c]] != ADD[MUL[a][b]][MUL[a][c]] || MUL[MUL[a][b]][c] != MUL[a][MUL[b][c]] ||
                    ADD[ADD[a][b]][c] != ADD[a][ADD[b][c]]) die("field axiom fails");
        }
        if (MUL[a][1] != a || ADD[a][0] != a || (a && inv < 0)) die("field axiom fails");
        INV[a] = (uint8_t)(a ? inv : 0);
    }
}

static int n, k;
static uint8_t *X, *Y;      /* X[r k + j], Y[r k + j]: the point of column j in row r */

static int M1, M2, R, GM[3][32][4], grp_ok = 1;
static long distinct;
static void mat_mul(const int *A, const int *B, int *C) {
    int c0 = ADD[MUL[A[0]][B[0]]][MUL[A[1]][B[2]]], c1 = ADD[MUL[A[0]][B[1]]][MUL[A[1]][B[3]]];
    int c2 = ADD[MUL[A[2]][B[0]]][MUL[A[3]][B[2]]], c3 = ADD[MUL[A[2]][B[1]]][MUL[A[3]][B[3]]];
    C[0] = c0; C[1] = c1; C[2] = c2; C[3] = c3;
}
static uint8_t DIR[MAXQ * MAXQ];
static void verify_group(void) {
    for (int r = 0; r < n; r++) {
        for (int g = 1; g <= 2; g++) {
            const int *G = GM[g][r];
            if (SUB[MUL[G[0]][G[3]]][MUL[G[1]][G[2]]] == 0) { fprintf(stderr, "row %d: G%d has determinant 0\n", r, g); grp_ok = 0; }
            int Pw[4] = {1, 0, 0, 1}, Mx = g == 1 ? M1 : M2;
            for (int t = 0; t < Mx; t++) mat_mul(Pw, G, Pw);
            if (Pw[0] != 1 || Pw[1] || Pw[2] || Pw[3] != 1) { fprintf(stderr, "row %d: G%d^%d != I\n", r, g, Mx); grp_ok = 0; }
            for (int x0 = 0; x0 < q; x0++) for (int y0 = 0; y0 < q; y0++)
                for (int d = 0; d <= q; d++) {  /* the line through (x0, y0) in direction (1, d), or (0, 1) when d = q */
                    if (d < q ? x0 != 0 : y0 != 0) continue;  /* each line once: from its point with x = 0 (or y = 0 when vertical) */
                    int dx = d < q ? 1 : 0, dy = d < q ? d : 1, ix0 = ADD[MUL[G[0]][x0]][MUL[G[1]][y0]], iy0 = ADD[MUL[G[2]][x0]][MUL[G[3]][y0]], dir0 = -1;
                    for (int t = 1; t < q; t++) {
                        int x = ADD[x0][MUL[t][dx]], y = ADD[y0][MUL[t][dy]];
                        int ix = ADD[MUL[G[0]][x]][MUL[G[1]][y]], iy = ADD[MUL[G[2]][x]][MUL[G[3]][y]];
                        int dd = DIR[SUB[ix][ix0] * q + SUB[iy][iy0]];
                        if (dd == WILD || (dir0 >= 0 && dd != dir0)) { grp_ok = 0; fprintf(stderr, "row %d: G%d breaks a line\n", r, g); t = q; d = q; x0 = q; y0 = q; }
                        dir0 = dd;
                    }
                }
        }
        int AB[4], BA[4];
        mat_mul(GM[1][r], GM[2][r], AB); mat_mul(GM[2][r], GM[1][r], BA);
        if (memcmp(AB, BA, sizeof AB)) { fprintf(stderr, "row %d: G1 G2 != G2 G1\n", r); grp_ok = 0; }
    }
}
static int cmpcol(const void *u, const void *v) {
    int a = *(const int *)u, b = *(const int *)v;
    for (int r = 0; r < n; r++) {
        int pa = X[(size_t)r * k + a] * q + Y[(size_t)r * k + a], pb = X[(size_t)r * k + b] * q + Y[(size_t)r * k + b];
        if (pa != pb) return pa < pb ? -1 : 1;
    }
    return 0;
}
static void expand(int *ids);
static void load(const char *file) {
    FILE *f = fopen(file, "r");
    if (!f) die("cannot open file");
    int *ids = NULL; size_t m = 0, cap = 0; int rows = 0, cols = -1, Rh = -1, nG[3] = {0, 0, 0};
    char *line = NULL; size_t lc = 0; ssize_t len;
    while ((len = getline(&line, &lc, f)) > 0) {
        if (!strncmp(line, "# orbit family:", 15)) {
            char *a = strstr(line, " M1 "), *b = strstr(line, " M2 "), *c = strstr(line, " reps ");
            if (!a || !b || !c) die("bad orbit header");
            M1 = atoi(a + 4); M2 = atoi(b + 4); Rh = atoi(c + 6);
            continue;
        }
        if (!strncmp(line, "# G1 ", 5) || !strncmp(line, "# G2 ", 5)) {
            int g = line[3] - '0', r, e0, e1, e2, e3;
            if (sscanf(line + 5, "%d %d %d %d %d", &r, &e0, &e1, &e2, &e3) != 5 || r < 0 || r >= 32) die("bad matrix line");
            int e[4] = {e0, e1, e2, e3};
            for (int i = 0; i < 4; i++) { if (e[i] < 0 || e[i] >= q) die("matrix entry out of range"); GM[g][r][i] = e[i]; }
            nG[g]++;
            continue;
        }
        if (line[0] < '0' || line[0] > '9') continue;
        int c = 0; char *s = line, *end;
        for (;;) {
            while (*s == ' ' || *s == '\t' || *s == '\r' || *s == '\n') s++;
            if (!*s) break;
            long v = strtol(s, &end, 10);
            if (end == s || v < q * q || v >= 2 * q * q) die("entry is not a vector (1, x, y)");
            if (m == cap) ids = realloc(ids, (cap = cap ? 2 * cap : 1 << 20) * sizeof *ids);
            ids[m++] = (int)v; c++; s = end;
        }
        if (cols < 0) cols = c; else if (c != cols) die("rows of different lengths");
        rows++;
    }
    fclose(f);
    n = rows; R = cols;
    if (n < 1 || n > 32 || R < 1 || M1 < 1 || M2 < 1 || Rh != R || nG[1] != n || nG[2] != n) die("incomplete orbit file");
    verify_group();
    expand(ids);
    free(ids);
}
static void expand(int *ids) {  /* ids: n rows of R representatives, ca-tools coding */
    long G = (long)M1 * M2, kl = (long)R * G;
    if (kl > 2000000000L) die("too many columns");
    k = (int)kl;
    X = malloc((size_t)n * k); Y = malloc((size_t)n * k);
    /* powers G1^i and G2^j, then column t G + i M2 + j = G1^i (G2^j c) */
    int (*P1)[4] = malloc(sizeof(int[4]) * M1), (*P2)[4] = malloc(sizeof(int[4]) * M2);
    for (int r = 0; r < n; r++) {
        P1[0][0] = 1; P1[0][1] = 0; P1[0][2] = 0; P1[0][3] = 1;
        for (int i = 1; i < M1; i++) mat_mul(P1[i - 1], GM[1][r], P1[i]);
        P2[0][0] = 1; P2[0][1] = 0; P2[0][2] = 0; P2[0][3] = 1;
        for (int j = 1; j < M2; j++) mat_mul(P2[j - 1], GM[2][r], P2[j]);
        for (int t = 0; t < R; t++) {
            int v = ids[(size_t)r * R + t] - q * q, cx = v / q, cy = v % q;
            for (int j = 0; j < M2; j++) {
                int ux = ADD[MUL[P2[j][0]][cx]][MUL[P2[j][1]][cy]], uy = ADD[MUL[P2[j][2]][cx]][MUL[P2[j][3]][cy]];
                for (int i = 0; i < M1; i++) {
                    size_t col = (size_t)t * G + (size_t)i * M2 + j;
                    X[(size_t)r * k + col] = (uint8_t)ADD[MUL[P1[i][0]][ux]][MUL[P1[i][1]][uy]];
                    Y[(size_t)r * k + col] = (uint8_t)ADD[MUL[P1[i][2]][ux]][MUL[P1[i][3]][uy]];
                }
            }
        }
    }
    free(P1); free(P2);
    int *ord = malloc(sizeof(int) * (size_t)k);
    for (int c = 0; c < k; c++) ord[c] = c;
    qsort(ord, (size_t)k, sizeof(int), cmpcol);
    distinct = k > 0;
    for (int c = 1; c < k; c++) distinct += cmpcol(&ord[c - 1], &ord[c]) != 0;
    free(ord);
}

static void make_dirs(void) {
    for (int dx = 0; dx < q; dx++)
        for (int dy = 0; dy < q; dy++)
            DIR[dx * q + dy] = (uint8_t)(!dx && !dy ? WILD : dx ? MUL[dy][INV[dx]] : q);  /* slope dy/dx, or vertical */
}

static int det3_nonzero(int r, int a, int b, int c) {  /* rows (1, x, y) of columns a, b, c in row r */
    int x1 = X[(size_t)r * k + a], y1 = Y[(size_t)r * k + a], x2 = X[(size_t)r * k + b], y2 = Y[(size_t)r * k + b],
        x3 = X[(size_t)r * k + c], y3 = Y[(size_t)r * k + c];
    /* det = (x2 y3 - x3 y2) - (x1 y3 - x3 y1) + (x1 y2 - x2 y1) */
    int t1 = SUB[MUL[x2][y3]][MUL[x3][y2]], t2 = SUB[MUL[x1][y3]][MUL[x3][y1]], t3 = SUB[MUL[x1][y2]][MUL[x2][y1]];
    return ADD[SUB[t1][t2]][t3] != 0;
}

struct wk { int c; int *buf[64], *srt[64], *wl[64]; uint8_t *lab[64]; long cp[64]; long long pairs, unc, internal, evals; int first[3]; long long *pb; int np, cap; };
static void ensure(struct wk *w, int d, long sz) {  /* buffers of depth d hold at least sz members */
    if (sz <= w->cp[d]) return;
    long c = sz + sz / 4 + 64;
    w->buf[d] = realloc(w->buf[d], sizeof(int) * c); w->srt[d] = realloc(w->srt[d], sizeof(int) * c);
    w->wl[d] = realloc(w->wl[d], sizeof(int) * c); w->lab[d] = realloc(w->lab[d], c);
    if (!w->buf[d] || !w->srt[d] || !w->wl[d] || !w->lab[d]) die("out of memory");
    w->cp[d] = c;
}
static int cmpll(const void *x, const void *y) { long long a = *(const long long *)x, b = *(const long long *)y; return (a > b) - (a < b); }
static void finish_c(struct wk *w) {  /* deduplicate, then confirm each pair by determinants */
    if (!w->np) return;
    qsort(w->pb, w->np, sizeof(long long), cmpll);
    for (int i = 0; i < w->np; i++) {
        if (i && w->pb[i] == w->pb[i - 1]) continue;
        int a = (int)(w->pb[i] >> 32), b = (int)(w->pb[i] & 0xFFFFFFFF), cov = 0;
        w->pairs++;
        for (int r = 0; r < n && !cov; r++) cov = det3_nonzero(r, a, b, w->c);
        if (cov) { w->internal++; continue; }
        if (!w->unc++) { w->first[0] = a; w->first[1] = b; w->first[2] = w->c; }
    }
    w->np = 0;
}

static void refine(struct wk *w, int depth, int *mem, int sz) {
    if (depth == n) {  /* collect the pairs; two wildcard columns can meet in several classes */
        for (int i = 0; i < sz; i++)
            for (int j = i + 1; j < sz; j++) {
                int a = mem[i] < mem[j] ? mem[i] : mem[j], b = mem[i] ^ mem[j] ^ a;
                if (w->np == w->cap) w->pb = realloc(w->pb, sizeof(long long) * (w->cap = w->cap ? 2 * w->cap : 1024));
                w->pb[w->np++] = (long long)a << 32 | (unsigned)b;
            }
        return;
    }
    if (sz <= 24) {  /* 16 Nov evening: a small class visits only the labels present (the loops over all q + 1 labels
                        cost most of the time at large q); the same child classes, members in the same order */
        int r = depth, ul[24], uc[24], nu = 0, nw = 0, wlist[24];
        uint8_t lab[24];
        const uint8_t *xr = X + (size_t)r * k, *yr = Y + (size_t)r * k;
        int cx = xr[w->c], cy = yr[w->c];
        w->evals += sz;
        for (int i = 0; i < sz; i++) {
            int j = mem[i];
            uint8_t l = DIR[SUB[xr[j]][cx] * q + SUB[yr[j]][cy]];
            lab[i] = l;
            if (l == WILD) { wlist[nw++] = j; continue; }
            int u = 0;
            while (u < nu && ul[u] != l) u++;
            if (u == nu) { ul[nu] = l; uc[nu++] = 0; }
            uc[u]++;
        }
        ensure(w, depth + 1, sz);
        int *child = w->buf[depth + 1];
        for (int u = 0; u < nu; u++) {
            if (uc[u] + nw < 2) continue;
            int m = 0;
            for (int i = 0; i < sz; i++) if (lab[i] == ul[u]) child[m++] = mem[i];
            for (int i = 0; i < nw; i++) child[m++] = wlist[i];
            refine(w, depth + 1, child, m);
        }
        if (!nu && nw >= 2) { memcpy(child, wlist, sizeof(int) * nw); refine(w, depth + 1, child, nw); }
        return;
    }
    ensure(w, depth, sz);
    int r = depth, cnt[MAXQ + 2] = {0}, start[MAXQ + 2];
    const uint8_t *xr = X + (size_t)r * k, *yr = Y + (size_t)r * k;
    int cx = xr[w->c], cy = yr[w->c];
    uint8_t *lb = w->lab[depth];
    w->evals += sz;
    for (int i = 0; i < sz; i++) {
        int j = mem[i];
        uint8_t l = DIR[SUB[xr[j]][cx] * q + SUB[yr[j]][cy]];
        lb[i] = l; cnt[l == WILD ? q + 1 : l]++;
    }
    int nw = cnt[q + 1], s = 0;
    for (int l = 0; l <= q; l++) { start[l] = s; s += cnt[l]; }
    int *srt = w->srt[depth], *wl = w->wl[depth], wi = 0;
    for (int i = 0; i < sz; i++) { if (lb[i] == WILD) wl[wi++] = mem[i]; else srt[start[lb[i]]++] = mem[i]; }
    ensure(w, depth + 1, sz);
    int *child = w->buf[depth + 1], any = 0;
    for (int l = 0, off = 0; l <= q; off += cnt[l], l++) {
        if (!cnt[l]) continue;
        any = 1;
        if (cnt[l] + nw < 2) continue;
        memcpy(child, srt + off, sizeof(int) * cnt[l]);
        memcpy(child + cnt[l], wl, sizeof(int) * nw);
        refine(w, depth + 1, child, cnt[l] + nw);
    }
    if (!any && nw >= 2) { memcpy(child, wl, sizeof(int) * nw); refine(w, depth + 1, child, nw); }
}

static int NEXTC = 0, NTH, ORBIT = 0;  /* ORBIT: anchors are the representatives t (column t M1 M2), members all others */
static pthread_mutex_t MX = PTHREAD_MUTEX_INITIALIZER;
static void *thr(void *arg) {
    struct wk *w = arg;
    for (;;) {
        pthread_mutex_lock(&MX);
        int t = NEXTC < (ORBIT ? R : k) ? NEXTC++ : -1;
        pthread_mutex_unlock(&MX);
        if (t < 0) break;
        int c = ORBIT ? (int)((long)t * M1 * M2) : t, m = 0;
        if (!ORBIT && c < 2) continue;
        w->c = c;
        int *mem = w->buf[0];
        if (ORBIT) { for (int j = 0; j < k; j++) if (j != c) mem[m++] = j; }
        else for (int j = 0; j < c; j++) mem[m++] = j;
        refine(w, 0, mem, m);
        finish_c(w);
    }
    return NULL;
}
static struct wk *newwk(void) {
    struct wk *w = calloc(1, sizeof *w);
    ensure(w, 0, k);  /* deeper levels grow on demand: a child class is never larger than its parent */
    return w;
}

static long long brute(void) {  /* every triple, for the self-test */
    long long u = 0;
    for (int a = 0; a < k; a++) for (int b = a + 1; b < k; b++) for (int c = b + 1; c < k; c++) {
        int cov = 0;
        for (int r = 0; r < n && !cov; r++) cov = det3_nonzero(r, a, b, c);
        u += !cov;
    }
    return u;
}

int main(int argc, char **argv) {
    if (argc < 3) die("usage: fullcheck3 q FILE [THREADS] | fullcheck3 q - selftest");
    q = atoi(argv[1]);
    field();
    make_dirs();
    if (!strcmp(argv[2], "-")) {  /* self-test: random arrays, Algorithm R against all triples */
        uint64_t s = 12345;
        for (int t = 0; t < 8; t++) {
            n = 1 + t % 4; k = 30 + t * 5;
            X = malloc((size_t)n * k); Y = malloc((size_t)n * k);
            for (int i = 0; i < n * k; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; X[i] = (uint8_t)(s % q); Y[i] = (uint8_t)((s >> 20) % q); }
            struct wk *w = newwk();
            long long fast = 0;
            for (int c = 2; c < k; c++) { w->c = c; for (int j = 0; j < c; j++) w->buf[0][j] = j; refine(w, 0, w->buf[0], c); finish_c(w); }
            fast = w->unc;
            long long b = brute();
            fprintf(stderr, "selftest q %d: %d rows, %d columns: brute force %lld, Algorithm R %lld uncovered triples%s\n", q, n, k, b, fast, b == fast && !w->internal ? "" : "  DISAGREE");
            if (b != fast || w->internal) return 1;
        }
        /* orbit self-test: random representatives under a random invertible A (G1 = A, G2 = A^e, orders computed);
           Algorithm R from each representative over all other columns against brute force over the same triples */
        for (int t = 0; t < 8; t++) {
            n = 1 + t % 4; R = 1 + t % 3;
            for (int r = 0; r < n; r++) {
                int A[4], D;
                do { for (int i = 0; i < 4; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; A[i] = (int)(s % q); } D = SUB[MUL[A[0]][A[3]]][MUL[A[1]][A[2]]]; } while (!D);
                memcpy(GM[1][r], A, sizeof A);
                s ^= s << 13; s ^= s >> 7; s ^= s << 17;
                int e = 1 + (int)(s % 3), B[4] = {1, 0, 0, 1};
                for (int i = 0; i < e; i++) mat_mul(B, A, B);
                memcpy(GM[2][r], B, sizeof B);
            }
            M1 = M2 = 1;  /* orders: the least m with every row's matrix^m = I */
            for (int g = 1; g <= 2; g++) {
                int m = 1, Pw[32][4];
                for (int r = 0; r < n; r++) memcpy(Pw[r], GM[g][r], sizeof Pw[r]);
                for (;; m++) {  /* Pw[r] = G_r^m */
                    int all = 1;
                    for (int r = 0; r < n; r++) all &= Pw[r][0] == 1 && !Pw[r][1] && !Pw[r][2] && Pw[r][3] == 1;
                    if (all) break;
                    for (int r = 0; r < n; r++) mat_mul(Pw[r], GM[g][r], Pw[r]);
                }
                if (g == 1) M1 = m; else M2 = m;
            }
            if ((long)R * M1 * M2 > 4000) { M2 = 1; for (int r = 0; r < n; r++) { GM[2][r][0] = 1; GM[2][r][1] = 0; GM[2][r][2] = 0; GM[2][r][3] = 1; } }
            if ((long)R * M1 * M2 > 4000) { t--; continue; }
            int *ids = malloc(sizeof(int) * n * R);
            for (int i = 0; i < n * R; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; ids[i] = q * q + (int)(s % (uint64_t)(q * q)); }
            grp_ok = 1; verify_group(); expand(ids); free(ids);
            struct wk *w = newwk();
            for (int u = 0; u < R; u++) {
                int c = u * M1 * M2, m = 0;
                w->c = c;
                for (int j = 0; j < k; j++) if (j != c) w->buf[0][m++] = j;
                refine(w, 0, w->buf[0], m); finish_c(w);
            }
            long long b = 0;
            for (int u = 0; u < R; u++) {
                int c = u * M1 * M2;
                for (int a = 0; a < k; a++) for (int bb = a + 1; bb < k; bb++) {
                    if (a == c || bb == c) continue;
                    int cov = 0;
                    for (int r = 0; r < n && !cov; r++) cov = det3_nonzero(r, a, bb, c);
                    b += !cov;
                }
            }
            fprintf(stderr, "orbit selftest q %d: %d rows, %d representatives, group %d x %d (%s), %d columns (%ld distinct): brute force %lld, Algorithm R %lld uncovered triples with a representative%s\n",
                    q, n, R, M1, M2, grp_ok ? "verified" : "GROUP TEST FAILED", k, distinct, b, w->unc, b == w->unc && !w->internal && grp_ok ? "" : "  DISAGREE");
            if (b != w->unc || w->internal || !grp_ok) return 1;
            free(X); free(Y);
        }
        return 0;
    }
    load(argv[2]);
    ORBIT = 1;
    NTH = argc > 3 ? atoi(argv[3]) : 1;
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    struct wk *W[64];
    pthread_t th[64];
    for (int i = 0; i < NTH; i++) { W[i] = newwk(); pthread_create(&th[i], NULL, thr, W[i]); }
    long long pairs = 0, unc = 0, internal = 0, evals = 0;
    int first[3] = {-1, -1, -1};
    for (int i = 0; i < NTH; i++) {
        pthread_join(th[i], NULL);
        pairs += W[i]->pairs; unc += W[i]->unc; internal += W[i]->internal; evals += W[i]->evals;
        if (W[i]->unc && first[0] < 0) memcpy(first, W[i]->first, sizeof first);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double secs = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
    long long triples = (long long)R * ((long long)(k - 1) * (k - 2) / 2);  /* R x C(k - 1, 2) */
    int fail = unc || !grp_ok || distinct != k;
    printf("orbit family: %d representatives, group Z_%d x Z_%d (%s), %d columns, %ld distinct\n", R, M1, M2,
           grp_ok ? "every matrix invertible and line-preserving, G1 G2 = G2 G1, G1^M1 = G2^M2 = I, every row" : "GROUP TEST FAILED", k, distinct);
    printf("SCPHF(%d; %d, %d, 3) (%s): all %lld triples that contain a representative decided by Algorithm R from each "
           "representative; %lld label evaluations, %lld surviving pairs confirmed by determinants, %lld uncovered, %lld internal "
           "disagreements; %d threads, %.0f s\n%s\n", n, k, q, argv[2], triples, evals, pairs, unc, internal, NTH, secs,
           internal ? "ERROR" : fail ? "FAIL" : "PASS");
    if (unc) printf("first uncovered triple: %d %d %d\n", first[0], first[1], first[2]);
    return internal ? 3 : fail ? 1 : 0;
}
