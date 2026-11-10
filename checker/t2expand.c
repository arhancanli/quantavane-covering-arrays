/* t2expand: expands an affine strength-2 CPHF (ca-tools format) into the covering array of Sherwood, Martirosyan and
   Colbourn with its own GF(q) arithmetic (prime q, or q in {4, 8, 9, 16, 25} by a fixed irreducible polynomial; the
   field structure on the point codes does not matter for coverage, only that it is a field), and checks the expanded
   ARRAY directly, with no CPHF reasoning: on a set S of columns, every pair of columns of S must show all q^2 pairs of
   symbols. S = the first W columns, then W random columns (seed), checked separately.
   Usage: t2expand FAMILY q W seed */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int q, p, e, mulT[32][32], addT[32][32];
static void build_field(void) {
    int poly = 0; /* coefficients of x^e term omitted; poly[i] for x^i, base p digits */
    p = q; e = 1;
    if (q == 4) { p = 2; e = 2; poly = 0x3; }        /* x^2 = x + 1 */
    else if (q == 8) { p = 2; e = 3; poly = 0x3; }   /* x^3 = x + 1 */
    else if (q == 16) { p = 2; e = 4; poly = 0x3; }  /* x^4 = x + 1 */
    else if (q == 9) { p = 3; e = 2; }               /* x^2 = -1 = 2 */
    else if (q == 25) { p = 5; e = 2; }              /* x^2 = 2 */
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        if (e == 1) { addT[a][b] = (a + b) % q; mulT[a][b] = (a * b) % q; continue; }
        int da[4], db[4], s = 0, pw = 1;
        for (int i = 0, x = a, y = b; i < e; i++, x /= p, y /= p) { da[i] = x % p; db[i] = y % p; }
        for (int i = 0; i < e; i++) { s += ((da[i] + db[i]) % p) * pw; pw *= p; }
        addT[a][b] = s;
        int prod[8] = {0};
        for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) prod[i + j] = (prod[i + j] + da[i] * db[j]) % p;
        for (int d = 2 * e - 2; d >= e; d--) {           /* reduce x^d = x^(d-e) * x^e */
            int c = prod[d]; prod[d] = 0; if (!c) continue;
            if (p == 2) { for (int i = 0; i < e; i++) if ((poly >> i) & 1) prod[d - e + i] ^= c; }
            else if (q == 9) prod[d - e] = (prod[d - e] + 2 * c) % 3;
            else if (q == 25) prod[d - e] = (prod[d - e] + 2 * c) % 5;
        }
        s = 0; pw = 1; for (int i = 0; i < e; i++) { s += (prod[i] % p) * pw; pw *= p; }
        mulT[a][b] = s;
    }
    /* field sanity: every nonzero element has an inverse, distributivity on all triples */
    for (int a = 1; a < q; a++) { int ok = 0; for (int b = 1; b < q; b++) if (mulT[a][b] == 1) ok++; if (ok != 1) { fprintf(stderr, "not a field\n"); exit(2); } }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++)
        if (mulT[a][addT[b][c]] != addT[mulT[a][b]][mulT[a][c]]) { fprintf(stderr, "not distributive\n"); exit(2); }
}
int main(int argc, char **argv) {
    if (argc != 5) { fprintf(stderr, "usage: t2expand FAMILY q W seed\n"); return 2; }
    q = atoi(argv[2]); int W = atoi(argv[3]); unsigned long long seed = strtoull(argv[4], 0, 10);
    build_field();
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    int n = 0; long k = -1; int **rows = malloc(64 * sizeof(int *));
    char *line = NULL; size_t lcap = 0;
    while (getline(&line, &lcap, f) > 0) {
        if (line[0] == '#' || line[0] == '\n') continue;
        long cap = 1024, cnt = 0; int *r = malloc(cap * sizeof(int)); char *s = line, *t;
        for (;;) { long x = strtol(s, &t, 10); if (t == s) break; if (cnt == cap) { cap *= 2; r = realloc(r, cap * sizeof(int)); } r[cnt++] = (int)(x - q); s = t; }
        if (k < 0) k = cnt; rows[n++] = r;
    }
    long N = (long)n * (q * q - q) + q;
    printf("family %s: n %d k %ld q %d -> expanded array %ld rows\n", argv[1], n, k, q, N);
    int *cols = malloc(sizeof(int) * 2 * W);
    for (int i = 0; i < W; i++) cols[i] = i;
    for (int i = 0; i < W; i++) { seed = seed * 6364136223846793005ULL + 1442695040888963407ULL; cols[W + i] = (int)((seed >> 33) % k); }
    for (int set = 0; set < 2; set++) {
        int *S = cols + set * W;
        /* expanded columns of S: A[c][row] */
        unsigned char *A = malloc((size_t)W * N);
        for (int ci = 0; ci < W; ci++) {
            long row = 0;
            for (int r = 0; r < n; r++) { int x = rows[r][S[ci]];
                for (int al = 1; al < q; al++) for (int be = 0; be < q; be++) A[(size_t)ci * N + row++] = (unsigned char)addT[mulT[al][x]][be]; }
            for (int be = 0; be < q; be++) A[(size_t)ci * N + row++] = (unsigned char)be;
        }
        unsigned long long pairs = 0, bad = 0; int bi = -1, bj = -1;
        unsigned char seen[1024];
        for (int i = 0; i < W; i++) for (int j = i + 1; j < W; j++) {
            if (S[i] == S[j]) continue;           /* the same column drawn twice */
            memset(seen, 0, q * q); int cntd = 0;
            const unsigned char *a = A + (size_t)i * N, *b = A + (size_t)j * N;
            for (long r = 0; r < N; r++) { int idx = a[r] * q + b[r]; if (!seen[idx]) { seen[idx] = 1; cntd++; } }
            pairs++; if (cntd != q * q) { if (!bad) { bi = S[i]; bj = S[j]; } bad++; }
        }
        printf("%s window of %d columns: %llu column pairs of the expanded array checked, %llu missing a symbol pair%s\n",
               set ? "random" : "first", W, pairs, bad, bad ? "" : " (all q^2 pairs present)");
        if (bad) { printf("first bad pair: columns %d %d\nRESULT FAIL\n", bi, bj); return 1; }
        free(A);
    }
    printf("RESULT PASS (expanded-array windows)\n");
    return 0;
}
