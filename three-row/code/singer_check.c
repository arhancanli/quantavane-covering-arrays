/* singer_check.c -- program 2 for Theorem K (family-theorems lane, 17 Nov 2026). Independent of kummer3.c: points
   are Singer exponents i in Z_N (alpha primitive in GF(q^3) built by singer.h from a cubic with no root, not from
   X^3 - c), collinearity from the planar difference set's line table. The array: columns (g, -g, g) and
   (g, t - g, g + t), t = N/3 (the Singer element of order 3, which is [b] for any b with b^3 in GF(q), b not in
   GF(q)). Checks every triple containing a g = 0 column (Z_N acts by translation in rows 1, 3 and by -g in row 2).
   usage: singer_check q [tshift]   (tshift != 0 replaces t by t + tshift: a red control) */
#include "singer.h"
int main(int argc, char **argv) {
    int q = atoi(argv[1]); int sh = argc > 2 ? atoi(argv[2]) : 0;
    if (!setup_singer(q)) { fprintf(stderr, "setup failed\n"); return 2; }
    if (N % 3) { printf("q %d: 3 does not divide N\n", q); return 1; }
    int t = (N / 3 + sh) % N, K = 2 * N;
    int *R0 = malloc(sizeof(int) * K), *R1 = malloc(sizeof(int) * K), *R2 = malloc(sizeof(int) * K);
    for (int g = 0; g < N; g++) { R0[g] = g; R1[g] = (N - g) % N; R2[g] = g;
        R0[N + g] = g; R1[N + g] = ((t - g) % N + N) % N; R2[N + g] = (g + t) % N; }
    long long bad = 0, tested = 0;
    for (int r = 0; r < 2; r++) { int c0 = r * N;
        for (int x = 0; x < K; x++) { if (x == c0) continue;
            for (int y = x + 1; y < K; y++) { if (y == c0) continue; tested++;
                if (covers(R0[c0], R0[x], R0[y]) || covers(R1[c0], R1[x], R1[y]) || covers(R2[c0], R2[x], R2[y])) continue;
                bad++; } } }
    printf("q %d N %d t %d k %d tested %lld uncovered %lld -> %s\n", q, N, t, K, tested, bad, bad ? "FAIL" : "PASS");
    return bad ? 1 : 0;
}
