/* singer_check2.c -- program 2 for Theorem K at large q (family-theorems lane, 17 Nov 2026). Same array and method
   as singer_check.c (Singer exponents from singer.h's own cubic and primitive alpha; collinearity from the planar
   difference set D), but with O(N) memory: pairdiff[d] = the unique (d1, d2) in D x D with d1 - d2 = d, so the line
   through points i != j is D + s with s = i - d1 (d = i - j), and k is on it iff k - s is in D.
   usage: NO_LINE_TABLE=1 singer_check2 q [tshift] */
#include "singer.h"
static int *PD1;
static inline int col3(int i, int j, int k) {
    int d = i - j; if (d < 0) d += N; int s = i - PD1[d]; if (s < 0) s += N; int e = k - s; if (e < 0) e += N; return inD[e];
}
static inline int cov(int i, int j, int k) { return i != j && j != k && i != k && !col3(i, j, k); }
int main(int argc, char **argv) {
    int q = atoi(argv[1]); int sh = argc > 2 ? atoi(argv[2]) : 0;
    if (!setup_singer(q)) { fprintf(stderr, "setup failed\n"); return 2; }
    if (N % 3) { printf("q %d: 3 does not divide N\n", q); return 1; }
    PD1 = malloc(sizeof(int) * N); for (int d = 0; d < N; d++) PD1[d] = -1;
    int D[2000], nd = 0; for (int i = 0; i < N; i++) if (inD[i]) D[nd++] = i;
    for (int x = 0; x < nd; x++) for (int y = 0; y < nd; y++) if (x != y) { int d = ((D[x] - D[y]) % N + N) % N;
        if (PD1[d] != -1) { fprintf(stderr, "not planar\n"); return 2; } PD1[d] = D[x]; }
    for (int d = 1; d < N; d++) if (PD1[d] < 0) { fprintf(stderr, "difference %d missing\n", d); return 2; }
    int t = (N / 3 + sh) % N, K = 2 * N;
    int *R0 = malloc(sizeof(int) * K), *R1 = malloc(sizeof(int) * K), *R2 = malloc(sizeof(int) * K);
    for (int g = 0; g < N; g++) { R0[g] = g; R1[g] = (N - g) % N; R2[g] = g;
        R0[N + g] = g; R1[N + g] = ((t - g) % N + N) % N; R2[N + g] = (g + t) % N; }
    long long bad = 0, tested = 0;
    for (int r = 0; r < 2; r++) { int c0 = r * N;
        for (int x = 0; x < K; x++) { if (x == c0) continue;
            for (int y = x + 1; y < K; y++) { if (y == c0) continue; tested++;
                if (cov(R0[c0], R0[x], R0[y]) || cov(R1[c0], R1[x], R1[y]) || cov(R2[c0], R2[x], R2[y])) continue;
                bad++; } } }
    printf("q %d N %d t %d k %d tested %lld uncovered %lld -> %s\n", q, N, t, K, tested, bad, bad ? "FAIL" : "PASS");
    return bad ? 1 : 0;
}
