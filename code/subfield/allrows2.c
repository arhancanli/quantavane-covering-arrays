/* allrows2: for q = 2^e and strength t = d+1, list every (d+1)-set J = {0 < j1 < ... < jd <= W} that is uncovered by
 * EVERY multiplicative row a^j, a in GF(q^d)^* (one row per class {a^(2^i)}; Proposition: such rows cover the same
 * sets). Field GF(2^(e d)) from a primitive polynomial found by search; F_q = {z : z^q = z}.
 * Affine dependence of points P_0..P_d over F_q <=> the d differences u_i = P_i - P_0 are F_q-dependent
 * <=> the e*d vectors w_k u_i (w_k = omega^k, k < e, omega a generator of F_q over F_2) have F_2-rank < e*d.
 * usage: allrows2 e d W
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int E, D, W, NB;
static uint32_t MOD;
static uint32_t mulf(uint32_t a, uint32_t b) {
  uint32_t r = 0;
  while (b) { if (b & 1) r ^= a; b >>= 1; a <<= 1; if (a >> NB) a ^= MOD; }
  return r;
}
int main(int argc, char **argv) {
  E = atoi(argv[1]); D = atoi(argv[2]); W = atoi(argv[3]);
  NB = E * D;
  uint32_t N = (1u << NB) - 1;
  /* primitive polynomial */
  for (uint32_t c = 1; c < (1u << NB); c += 2) {
    MOD = (1u << NB) | c;
    uint32_t v = 1, k;
    for (k = 1; k <= N; k++) { v = mulf(v, 2); if (v == 1) break; }
    if (k == N) break;
  }
  uint32_t *pw = malloc(sizeof(uint32_t) * N);
  pw[0] = 1; for (uint32_t i = 1; i < N; i++) pw[i] = mulf(pw[i - 1], 2);
  uint32_t qm1 = (1u << E) - 1;
  uint32_t step = N / qm1;              /* theta^step generates F_q^* */
  uint32_t omega = pw[step];             /* omega generates F_q over F_2 (primitive element of F_q) */
  uint32_t wk[8]; wk[0] = 1; for (int k = 1; k < E; k++) wk[k] = mulf(wk[k - 1], omega);
  /* row representatives: exponents b mod N, one per orbit under b -> 2b */
  char *seen = calloc(N, 1); int nrows = 0; uint32_t *reps = malloc(sizeof(uint32_t) * N);
  for (uint32_t b = 1; b < N; b++) { if (seen[b]) continue; uint32_t c = b; while (!seen[c]) { seen[c] = 1; c = (uint32_t)(((uint64_t)c * 2) % N); } reps[nrows++] = b; }
  /* b = 0 (a = 1) row: all points equal 1 -> covers nothing; skip */
  /* precompute per row the points and their omega multiples */
  uint32_t *pts = malloc(sizeof(uint32_t) * (size_t)nrows * (W + 1) * E);
  for (int r = 0; r < nrows; r++) for (int j = 0; j <= W; j++) {
    uint32_t P = pw[(uint32_t)(((uint64_t)reps[r] * j) % N)];
    for (int k = 0; k < E; k++) pts[((size_t)r * (W + 1) + j) * E + k] = mulf(P, wk[k]);
  }
  fprintf(stderr, "q=%u d=%d W=%d rows=%d\n", qm1 + 1, D, W, nrows);
  int J[16]; int idx[16];
  long long tested = 0, found = 0;
  for (int i = 1; i <= D; i++) idx[i] = i;
  J[0] = 0;
  int target = E * D;
  while (1) {
    for (int i = 1; i <= D; i++) J[i] = idx[i];
    tested++;
    int covered = 0;
    for (int r = 0; r < nrows && !covered; r++) {
      uint32_t basis[32] = {0}; int rk = 0;
      const uint32_t *base = pts + (size_t)r * (W + 1) * E;
      for (int i = 1; i <= D; i++) for (int k = 0; k < E; k++) {
        uint32_t v = base[J[i] * E + k] ^ base[J[0] * E + k];
        while (v) { int h = 31 - __builtin_clz(v); if (basis[h]) v ^= basis[h]; else { basis[h] = v; rk++; break; } }
      }
      if (rk == target) covered = 1;
    }
    if (!covered) {
      found++;
      printf("J=");
      for (int i = 0; i <= D; i++) printf("%d%s", J[i], i < D ? "," : "\n");
      fflush(stdout);
    }
    int i = D; while (i >= 1 && idx[i] == W - (D - i)) i--;
    if (i < 1) break;
    idx[i]++; for (int j = i + 1; j <= D; j++) idx[j] = idx[j - 1] + 1;
  }
  fprintf(stderr, "tested=%lld universal=%lld\n", tested, found);
  return 0;
}
