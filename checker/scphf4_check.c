/* Independent check of a strength-4 Sherwood CPHF (engine/native/cphf4x.c output). Field arithmetic as in
   independent/scphf_check.c (Horner multiplication modulo the listed polynomial, field axioms tested before use),
   written apart from the search; points of AG(3,q) as ids (x q + y) q + z.
   1. Every four columns a < b < c < d must hold, in some row, points A, B, C, D with det(B - A, C - A, D - A) != 0
      (not on one plane). Two exact methods: "brute" tries all C(k,4) sets; "cells" (for large k) lists only the
      sets on one plane in each of the first M rows: columns are bucketed by every plane through their point in row
      0, each bucket again by every plane through the point in row 1, and so on; a set lies on one plane in each of
      those rows exactly when it shares a bucket at depth M, so the sets at depth M are tested in rows M..n-1 and no
      other set can fail. A failing set is counted once, in the bucket path of the smallest planes holding it.
      Default: brute when C(k,4) <= 1e10, else cells (METHOD = brute or cells forces one; threads from CHECK_THREADS).
   2. Spot check of the covering array it gives, CA(n(q^4 - q) + q; 4, k, q) (row (u0,u1,u2,u3) of block r puts
      u0 + u1 x + u2 y + u3 z in a column whose point in row r is (x, y, z); the q constant rows once): for SAMPLES
      random sets of four columns (default 500), every one of the q^4 tuples of symbols must appear.
   cc -O3 -o scphf4_check scphf4_check.c -lpthread && ./scphf4_check q FILE [SAMPLES] [METHOD] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <pthread.h>
#include <unistd.h>

#define MAXQ 32
#define MAXN 32
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
        p = q; m = 1; poly[0] = 0; poly[1] = 1;  /* GF(p): x^1 = 0 never used; times_x is not reached */
        for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { ADD[a][b] = (a + b) % q; MUL[a][b] = a * b % q; }
    } else {
        for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { ADD[a][b] = padd(a, b); MUL[a][b] = pmul(a, b); }
    }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) if (ADD[b][c] == a) SUB[a][b] = c;
    /* field axioms: inverses exist, multiplication associative and commutative, distributive over addition */
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
static uint8_t *X[MAXN], *Y[MAXN], *Z[MAXN];
static int NV, NPL, M;               /* plane normals (q^2 + q + 1), planes (q NV), rows used for buckets */
static uint8_t NA[MAXQ * MAXQ + MAXQ + 1][3];

static inline int plane_of(int i, int r, int c) {  /* id of the plane with normal i through column c's point in row r */
    return i * q + ADD[ADD[MUL[NA[i][0]][X[r][c]]][MUL[NA[i][1]][Y[r][c]]]][MUL[NA[i][2]][Z[r][c]]];
}

static inline int indep(int r, int a, int b, int c, int d) {
    int u0 = SUB[X[r][b]][X[r][a]], u1 = SUB[Y[r][b]][Y[r][a]], u2 = SUB[Z[r][b]][Z[r][a]];
    int v0 = SUB[X[r][c]][X[r][a]], v1 = SUB[Y[r][c]][Y[r][a]], v2 = SUB[Z[r][c]][Z[r][a]];
    int w0 = SUB[MUL[u1][v2]][MUL[u2][v1]], w1 = SUB[MUL[u2][v0]][MUL[u0][v2]], w2 = SUB[MUL[u0][v1]][MUL[u1][v0]];
    return ADD[ADD[MUL[w0][SUB[X[r][d]][X[r][a]]]][MUL[w1][SUB[Y[r][d]][Y[r][a]]]]][MUL[w2][SUB[Z[r][d]][Z[r][a]]]] != 0;
}

struct tl {  /* one thread's buffers, one set per depth */
    int *pid[MAXN], *ent[MAXN], *cnt[MAXN], *off[MAXN], *touched[MAXN];
    int path[MAXN];
    long long sets, bad;
    int first[4];
};

static int canonical(const struct tl *T, int a, int b, int c, int d) {
    for (int r = 0; r < M; r++) {
        int best = INT_MAX;
        for (int i = 0; i < NV; i++) {
            int pa = plane_of(i, r, a);
            if (pa < best && pa == plane_of(i, r, b) && pa == plane_of(i, r, c) && pa == plane_of(i, r, d)) best = pa;
        }
        if (best != T->path[r]) return 0;
    }
    return 1;
}

static void leaf(struct tl *T, const int *L, int s) {
    for (int x = 0; x < s; x++)
        for (int y = x + 1; y < s; y++)
            for (int z = y + 1; z < s; z++)
                for (int t = z + 1; t < s; t++) {
                    int a = L[x], b = L[y], c = L[z], d = L[t], ok = 0;
                    for (int r = M; r < n && !ok; r++) ok = indep(r, a, b, c, d);
                    T->sets++;
                    if (!ok && canonical(T, a, b, c, d)) {
                        if (!T->bad) { T->first[0] = a; T->first[1] = b; T->first[2] = c; T->first[3] = d; }
                        T->bad++;
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
        if (c >= 4) { T->path[lev] = pl; rec(T, lev + 1, ent + off[pl] - c, c); }
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
        if (c >= 4) { T->path[0] = pl; rec(T, 1, b0list + b0start[pl], c); }
    }
}

static void cells_check(long long *sets, long long *bad, int first[4]) {
    NV = 0;
    for (int a0 = 0; a0 < 2; a0++)
        for (int a1 = 0; a1 < q; a1++)
            for (int a2 = 0; a2 < q; a2++) {
                if (a0 == 0 && (a1 > 1 || (a1 == 0 && a2 != 1))) continue;  /* first nonzero coordinate is 1 */
                NA[NV][0] = (uint8_t)a0; NA[NV][1] = (uint8_t)a1; NA[NV][2] = (uint8_t)a2; NV++;
            }
    NPL = NV * q;
    double c4 = (double)k * (k - 1) * (k - 2) * (k - 3) / 24, bestcost = 1e300;
    for (int m = 1; m <= n; m++) {  /* bucket entries (about k NV^m) plus sets at depth m (about C(k,4) / q^m) */
        double cost = (double)k * pow_int(NV, m) + 3 * c4 / pow_int(q, m);
        if (cost < bestcost) { bestcost = cost; M = m; }
    }
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
        pthread_create(&th[w], NULL, worker, &TL[w]);
    }
    *sets = *bad = 0;
    first[0] = -1;
    for (int w = 0; w < nth; w++) {
        pthread_join(th[w], NULL);
        *sets += TL[w].sets;
        if (TL[w].bad && first[0] < 0) memcpy(first, TL[w].first, sizeof(int) * 4);
        *bad += TL[w].bad;
    }
    printf("cells method: %d rows bucketed by planes, %d threads\n", M, nth);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: scphf4_check q FILE [SAMPLES] [brute|cells]\n"); return 2; }
    q = atoi(argv[1]);
    long samples = argc > 3 ? atol(argv[3]) : 500;
    if (q < 2 || q > MAXQ || !setup()) { fprintf(stderr, "q is not a supported field order\n"); return 2; }
    FILE *f = fopen(argv[2], "r");
    if (!f) { perror(argv[2]); return 2; }
    static char line[1 << 22];
    k = -1;
    while (fgets(line, sizeof line, f)) {
        if (line[0] < '0' || line[0] > '9') continue;
        if (n == MAXN) { fprintf(stderr, "too many rows\n"); return 2; }
        int c = 0;
        X[n] = malloc(MAXK); Y[n] = malloc(MAXK); Z[n] = malloc(MAXK);
        for (char *s = strtok(line, " \t\n"); s; s = strtok(NULL, " \t\n")) {
            int id = atoi(s);
            if (id < 0 || id >= q * q * q || c == MAXK) { fprintf(stderr, "bad point id or too many columns\n"); return 2; }
            X[n][c] = (uint8_t)(id / (q * q)); Y[n][c] = (uint8_t)(id / q % q); Z[n][c] = (uint8_t)(id % q); c++;
        }
        if (k >= 0 && c != k) { fprintf(stderr, "rows differ in length\n"); return 2; }
        k = c; n++;
    }
    fclose(f);
    if (n < 1 || k < 4) { fprintf(stderr, "no array\n"); return 2; }
    /* 1. geometry, every set of four columns */
    long long sets = 0, bad = 0;
    int fa = -1, fb = -1, fc = -1, fd = -1;
    double c4 = (double)k * (k - 1) * (k - 2) * (k - 3) / 24;
    const char *method = argc > 4 ? argv[4] : (c4 <= 1e10 ? "brute" : "cells");
    if (!strcmp(method, "cells")) {
        int first[4];
        cells_check(&sets, &bad, first);
        fa = first[0]; fb = first[1]; fc = first[2]; fd = first[3];
    } else if (strcmp(method, "brute")) { fprintf(stderr, "method is brute or cells\n"); return 2; }
    else
    for (int a = 0; a < k; a++)
        for (int b = a + 1; b < k; b++) {
            int u[MAXN][3];
            for (int r = 0; r < n; r++) { u[r][0] = SUB[X[r][b]][X[r][a]]; u[r][1] = SUB[Y[r][b]][Y[r][a]]; u[r][2] = SUB[Z[r][b]][Z[r][a]]; }
            for (int c = b + 1; c < k; c++) {
                int w[MAXN][3];  /* (B - A) x (C - A) per row */
                for (int r = 0; r < n; r++) {
                    int v0 = SUB[X[r][c]][X[r][a]], v1 = SUB[Y[r][c]][Y[r][a]], v2 = SUB[Z[r][c]][Z[r][a]];
                    w[r][0] = SUB[MUL[u[r][1]][v2]][MUL[u[r][2]][v1]];
                    w[r][1] = SUB[MUL[u[r][2]][v0]][MUL[u[r][0]][v2]];
                    w[r][2] = SUB[MUL[u[r][0]][v1]][MUL[u[r][1]][v0]];
                }
                for (int d = c + 1; d < k; d++) {
                    int ok = 0;
                    for (int r = 0; r < n && !ok; r++)
                        ok = ADD[ADD[MUL[w[r][0]][SUB[X[r][d]][X[r][a]]]][MUL[w[r][1]][SUB[Y[r][d]][Y[r][a]]]]][MUL[w[r][2]][SUB[Z[r][d]][Z[r][a]]]] != 0;
                    sets++;
                    if (!ok) { if (!bad) { fa = a; fb = b; fc = c; fd = d; } bad++; }
                }
            }
        }
    printf("SCPHF(%d; %d, %d^3, 4): %lld sets of four columns %s, %lld always on one plane", n, k, q, sets,
           strcmp(method, "cells") ? "checked" : "tested (the rest leave one plane in a bucketed row)", bad);
    if (bad) printf(" (first: columns %d, %d, %d, %d)", fa, fb, fc, fd);
    printf("\n");
    /* 2. covering-array spot check */
    long N = (long)n * (q * q * q * q - q) + q, missing = 0;
    int Q4 = q * q * q * q;
    uint32_t *stamp = calloc(Q4, sizeof(uint32_t));
    uint64_t s = 0x2545F4914F6CDD1DULL;
    for (long t = 1; t <= samples; t++) {
        int col[4];
        for (;;) {
            for (int i = 0; i < 4; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; col[i] = (int)(s % (uint64_t)k); }
            int dup = 0;
            for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) dup |= col[i] == col[j];
            if (!dup) break;
        }
        int seen = 0;
        for (int r = 0; r < n; r++)
            for (int u1 = 0; u1 < q; u1++)
                for (int u2 = 0; u2 < q; u2++)
                    for (int u3 = 0; u3 < q; u3++) {
                        if (!u1 && !u2 && !u3 && r > 0) continue;  /* constant rows once */
                        int base[4];
                        for (int i = 0; i < 4; i++)
                            base[i] = ADD[ADD[MUL[u1][X[r][col[i]]]][MUL[u2][Y[r][col[i]]]]][MUL[u3][Z[r][col[i]]]];
                        for (int u0 = 0; u0 < q; u0++) {
                            int code = ((ADD[u0][base[0]] * q + ADD[u0][base[1]]) * q + ADD[u0][base[2]]) * q + ADD[u0][base[3]];
                            if (stamp[code] != (uint32_t)t) { stamp[code] = (uint32_t)t; seen++; }
                        }
                    }
        if (seen != Q4) missing++;
    }
    printf("CA(%ld; 4, %d, %d): %ld random sets of four columns, %ld missing a tuple\n", N, k, q, samples, missing);
    printf("%s\n", bad || missing ? "FAIL" : "PASS");
    return bad || missing ? 1 : 0;
}
