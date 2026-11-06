/* fullcheck3.c: exact check of a strength-3 Sherwood CPHF given as a ca-tools certificate (Conway coding), written
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

#define MAXQ 32
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
static uint8_t DIR[MAXQ * MAXQ];  /* direction index (0..q) of a nonzero difference vector (dx, dy); WILD for (0,0) */

static void load(const char *file) {
    FILE *f = fopen(file, "r");
    if (!f) die("cannot open file");
    int *ids = NULL; size_t m = 0, cap = 0; int rows = 0, cols = -1;
    char *line = NULL; size_t lc = 0; ssize_t len;
    while ((len = getline(&line, &lc, f)) > 0) {
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
    n = rows; k = cols;
    X = malloc((size_t)n * k); Y = malloc((size_t)n * k);
    for (size_t i = 0; i < m; i++) { int v = ids[i] - q * q; X[i] = (uint8_t)(v / q); Y[i] = (uint8_t)(v % q); }
    free(ids);
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

struct wk { int c; int *buf[64], *srt[64], *wl[64]; uint8_t *lab[64]; long long pairs, unc, internal, evals; int first[3]; long long *pb; int np, cap; };
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

static int NEXTC = 2, NTH;
static pthread_mutex_t MX = PTHREAD_MUTEX_INITIALIZER;
static void *thr(void *arg) {
    struct wk *w = arg;
    for (;;) {
        pthread_mutex_lock(&MX);
        int c = NEXTC < k ? NEXTC++ : -1;
        pthread_mutex_unlock(&MX);
        if (c < 0) break;
        w->c = c;
        int *mem = w->buf[0];
        for (int j = 0; j < c; j++) mem[j] = j;
        refine(w, 0, mem, c);
        finish_c(w);
    }
    return NULL;
}
static struct wk *newwk(void) {
    struct wk *w = calloc(1, sizeof *w);
    for (int d = 0; d < 64; d++) { w->buf[d] = malloc(sizeof(int) * k); w->srt[d] = malloc(sizeof(int) * k); w->wl[d] = malloc(sizeof(int) * k); w->lab[d] = malloc(k); }
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
        return 0;
    }
    load(argv[2]);
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
    long long triples = (long long)k * (k - 1) / 2 * (k - 2) / 3;  /* C(k, 3) */
    printf("SCPHF(%d; %d, %d, 3) (%s): all %lld triples of columns decided by Algorithm R from each largest column; "
           "%lld label evaluations, %lld surviving pairs confirmed by determinants, %lld uncovered, %lld internal "
           "disagreements; %d threads, %.0f s\n%s\n", n, k, q, argv[2], triples, evals, pairs, unc, internal, NTH, secs,
           internal ? "ERROR" : unc ? "FAIL" : "PASS");
    if (unc) printf("first uncovered triple: %d %d %d\n", first[0], first[1], first[2]);
    return internal ? 3 : unc ? 1 : 0;
}
