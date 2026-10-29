/* Independent check of a strength-3 Sherwood CPHF, for arrays too large for independent/cphf_check.py and
   independent/ca_check.c. Written apart from engine/native/cphf3.c: its own field arithmetic (Horner multiplication
   modulo the listed polynomial, with the field axioms tested before use) and a direct determinant test.
   Input: q, then a file whose lines that start with a digit are the n rows of k point ids x*q + y (field elements
   as base-p digit vectors, digit i the coefficient of x^i).
   1. Every three columns a < b < c must hold, in some row, points with det [[1,xa,ya],[1,xb,yb],[1,xc,yc]] != 0
      (three distinct points not on one line). All C(k,3) triples are checked.
   2. Spot check of the covering array it gives, CA(n(q^3 - q) + q; 3, k, q) (row (u0,u1,u2) of block r puts
      u0 + u1 x + u2 y in a column whose point in row r is (x, y); the q constant rows once): for SAMPLES random
      column triples (default 2000), every one of the q^3 triples of symbols must appear.
   cc -O3 -o scphf_check scphf_check.c && ./scphf_check q FILE [SAMPLES] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXQ 32
#define MAXN 16

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

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: scphf_check q FILE [SAMPLES]\n"); return 2; }
    q = atoi(argv[1]);
    long samples = argc > 3 ? atol(argv[3]) : 2000;
    if (q < 2 || q > MAXQ || !setup()) { fprintf(stderr, "q is not a supported field order\n"); return 2; }
    FILE *f = fopen(argv[2], "r");
    if (!f) { perror(argv[2]); return 2; }
    static char line[1 << 20];
    int n = 0, k = -1;
    uint8_t *X[MAXN], *Y[MAXN];
    while (fgets(line, sizeof line, f)) {
        if (line[0] < '0' || line[0] > '9') continue;
        if (strncmp(line, "best", 4) == 0) continue;
        if (n == MAXN) { fprintf(stderr, "too many rows\n"); return 2; }
        int cap = 1 << 16, c = 0;
        X[n] = malloc(cap); Y[n] = malloc(cap);
        for (char *s = strtok(line, " \t\n"); s; s = strtok(NULL, " \t\n")) {
            int id = atoi(s);
            if (id < 0 || id >= q * q || c == cap) { fprintf(stderr, "bad point id or too many columns\n"); return 2; }
            X[n][c] = (uint8_t)(id / q); Y[n][c] = (uint8_t)(id % q); c++;
        }
        if (k >= 0 && c != k) { fprintf(stderr, "rows differ in length\n"); return 2; }
        k = c; n++;
    }
    fclose(f);
    if (n < 1 || k < 3) { fprintf(stderr, "no array\n"); return 2; }
    /* 1. geometry, every triple */
    long long triples = 0, badt = 0;
    int fa = -1, fb = -1, fc = -1;
    for (int a = 0; a < k; a++)
        for (int b = a + 1; b < k; b++) {
            int dx[MAXN], dy[MAXN];
            for (int r = 0; r < n; r++) { dx[r] = SUB[X[r][b]][X[r][a]]; dy[r] = SUB[Y[r][b]][Y[r][a]]; }
            for (int c = b + 1; c < k; c++) {
                int ok = 0;
                for (int r = 0; r < n && !ok; r++)
                    ok = SUB[MUL[dx[r]][SUB[Y[r][c]][Y[r][a]]]][MUL[dy[r]][SUB[X[r][c]][X[r][a]]]] != 0;
                triples++;
                if (!ok) { if (!badt) { fa = a; fb = b; fc = c; } badt++; }
            }
        }
    printf("SCPHF(%d; %d, %d^2, 3): %lld column triples checked, %lld never non-collinear", n, k, q, triples, badt);
    if (badt) printf(" (first: columns %d, %d, %d)", fa, fb, fc);
    printf("\n");
    /* 2. covering-array spot check */
    long N = (long)n * (q * q * q - q) + q, missing = 0;
    int Q3 = q * q * q;
    uint32_t *stamp = calloc(Q3, sizeof(uint32_t));
    uint64_t s = 0x2545F4914F6CDD1DULL;
    for (long t = 1; t <= samples; t++) {
        int col[3];
        do {
            for (int i = 0; i < 3; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; col[i] = (int)(s % (uint64_t)k); }
        } while (col[0] == col[1] || col[0] == col[2] || col[1] == col[2]);
        int seen = 0;
        for (int r = 0; r < n; r++)
            for (int u1 = 0; u1 < q; u1++)
                for (int u2 = 0; u2 < q; u2++) {
                    if (u1 == 0 && u2 == 0 && r > 0) continue;  /* constant rows once */
                    int base[3];
                    for (int i = 0; i < 3; i++) base[i] = ADD[MUL[u1][X[r][col[i]]]][MUL[u2][Y[r][col[i]]]];
                    for (int u0 = 0; u0 < q; u0++) {
                        int code = (ADD[u0][base[0]] * q + ADD[u0][base[1]]) * q + ADD[u0][base[2]];
                        if (stamp[code] != (uint32_t)t) { stamp[code] = (uint32_t)t; seen++; }
                    }
                }
        if (seen != Q3) missing++;
    }
    printf("CA(%ld; 3, %d, %d): %ld random column triples, %ld missing a tuple\n", N, k, q, samples, missing);
    printf("%s\n", badt || missing ? "FAIL" : "PASS");
    return badt || missing ? 1 : 0;
}
