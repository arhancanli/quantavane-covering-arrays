/* univ.c -- referee's own direct computation (does NOT use the subfield criterion of the paper).
 * Lists the base sets J = w*M (M a set of d+1 integers, 0 in M, max M <= W, max M >= Wmin) that are covered by
 * NO multiplicative row j -> a^j of L = GF(q^d), q = p^e, i.e. for which the d+1 points a^{w m} are affinely
 * dependent over F_q for every a in L^*.  (Rows z a^j are equivalent to a^j; rows a^j and (a^p)^j are equivalent,
 * so one a per Frobenius orbit of exponents is used for the final "all rows" pass.)
 * F_q-independence of the d differences D_k is tested as F_p-rank N = e*d of the vectors omega^i D_k (i < e),
 * omega a generator of F_q^*.
 * usage: univ p e d w W [Wmin] [maxprint]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define MAXN 24
static int p, e, d, N, W, Wmin = 0, maxprint = 50;
static long long q, Lsize, ordL, wq, w;
static int32_t *alog, *lg;
static int32_t pw_[MAXN + 1];
static uint64_t ONES, K8p, H8;
static int invp[16];

/* ---------- polynomial arithmetic over F_p for the primitive-polynomial search ---------- */
static void pmulmod(const int *a, const int *b, const int *f, int *out) { /* a*b mod f, deg < N, f monic deg N */
  int t[2 * MAXN];
  memset(t, 0, sizeof t);
  for (int i = 0; i < N; i++) if (a[i]) for (int j = 0; j < N; j++) t[i + j] = (t[i + j] + a[i] * b[j]) % p;
  for (int k = 2 * N - 2; k >= N; k--) if (t[k]) { int c = t[k]; for (int i = 0; i <= N; i++) t[k - N + i] = ((t[k - N + i] - c * f[i]) % p + p) % p; }
  for (int i = 0; i < N; i++) out[i] = t[i];
}
static int xpow_is_one(const int *f, long long ex) {
  int r[MAXN] = {0}, b[MAXN] = {0}, tmp[MAXN];
  r[0] = 1; b[1] = 1;
  while (ex) { if (ex & 1) { pmulmod(r, b, f, tmp); memcpy(r, tmp, sizeof r); } pmulmod(b, b, f, tmp); memcpy(b, tmp, sizeof b); ex >>= 1; }
  if (r[0] != 1) return 0; for (int i = 1; i < N; i++) if (r[i]) return 0; return 1;
}
static int is_primitive(const int *f) {
  if (!xpow_is_one(f, ordL)) return 0;
  long long n = ordL;
  for (long long l = 2; l * l <= n; l++) if (n % l == 0) { if (xpow_is_one(f, ordL / l)) return 0; while (n % l == 0) n /= l; }
  if (n > 1 && xpow_is_one(f, ordL / n)) return 0;
  return 1;
}

static void build_field(void) {
  int f[MAXN + 1];
  long long ncodes = 1; for (int i = 0; i < N; i++) ncodes *= p;
  int found = 0;
  for (long long code = 1; code < ncodes && !found; code++) {
    long long c = code; for (int i = 0; i < N; i++) { f[i] = c % p; c /= p; } f[N] = 1;
    if (f[0] == 0) continue;
    if (is_primitive(f)) found = 1;
  }
  if (!found) { fprintf(stderr, "no primitive polynomial\n"); exit(1); }
  fprintf(stderr, "L = GF(%d^%d), primitive f (low first):", p, N); for (int i = 0; i <= N; i++) fprintf(stderr, " %d", f[i]); fprintf(stderr, "\n");
  alog = malloc(sizeof(int32_t) * (size_t)ordL); lg = malloc(sizeof(int32_t) * (size_t)Lsize);
  for (long long i = 0; i < Lsize; i++) lg[i] = -1;
  int dg[MAXN]; memset(dg, 0, sizeof dg); dg[0] = 1;
  for (long long k = 0; k < ordL; k++) {
    int32_t v = 0; for (int i = 0; i < N; i++) v += dg[i] * pw_[i];
    if (lg[v] != -1) { fprintf(stderr, "not primitive?\n"); exit(1); }
    alog[k] = v; lg[v] = (int32_t)k;
    int top = dg[N - 1];
    for (int i = N - 1; i > 0; i--) dg[i] = dg[i - 1]; dg[0] = 0;
    if (top) for (int i = 0; i < N; i++) dg[i] = ((dg[i] - top * f[i]) % p + p) % p;
  }
  { int32_t v = 0; for (int i = 0; i < N; i++) v += dg[i] * pw_[i]; if (v != 1) { fprintf(stderr, "order error\n"); exit(1); } }
}

/* ---------- vectors: p = 2 bit vectors; odd p nibble-packed digits ---------- */
static inline uint64_t tovec(int32_t v) {
  if (p == 2) return (uint64_t)v;
  uint64_t r = 0; for (int i = 0; i < N; i++) { r |= (uint64_t)(v % p) << (4 * i); v /= p; } return r;
}
static inline uint64_t addp(uint64_t a, uint64_t b) { uint64_t s = a + b; uint64_t m = ((s + K8p) & H8) >> 3; return s - m * (uint64_t)p; }
static inline uint64_t scal(uint64_t v, int c) { uint64_t r = 0; for (int i = 0; i < N; i++) { uint64_t dd = (v >> (4 * i)) & 15; r |= (uint64_t)((dd * c) % p) << (4 * i); } return r; }

typedef struct { uint64_t piv[MAXN]; uint64_t mul[16][6]; } basis_t;

/* insert v; return pivot index used, or -1 if v is in the span */
static inline int ins(basis_t *B, uint64_t v) {
  if (p == 2) {
    while (v) { int b = 63 - __builtin_clzll(v); if (!B->piv[b]) { B->piv[b] = v; return b; } v ^= B->piv[b]; }
    return -1;
  }
  for (int b = N - 1; b >= 0; b--) {
    int c = (int)((v >> (4 * b)) & 15);
    if (!c) continue;
    if (B->piv[b]) v = addp(v, B->mul[b][p - c]);
    else { uint64_t nv = scal(v, invp[c]); B->piv[b] = nv; for (int cc = 1; cc < p; cc++) B->mul[b][cc] = scal(nv, cc); return b; }
  }
  return -1;
}

static inline int32_t minus_one(int32_t P) {
  if (p == 2) return P ^ 1;
  int d0 = P % p; return P - d0 + ((d0 - 1 + p) % p);
}

/* full coverage test of M in the row with exponent alpha (a = g^alpha): 1 if covered */
static int covered_row(const int *Mv, long long alpha) {
  basis_t B; memset(B.piv, 0, sizeof B.piv);
  for (int k = 1; k <= d; k++) {
    long long ex = (alpha % ordL) * ((w * (long long)Mv[k]) % ordL) % ordL;
    int32_t D = minus_one(alog[ex]);
    if (D == 0) return 0;
    long long l = lg[D];
    for (int i = 0; i < e; i++) { int32_t x = alog[(l + (long long)i * wq) % ordL]; if (ins(&B, tovec(x)) < 0) return 0; }
  }
  return 1;
}

static long long *reps; static long long nreps;
static long long quick[64]; static int nquick;
static uint64_t (*V1)[8]; static char *bad1; /* primary row alpha = 1 */
static int M[16]; static basis_t B; static int dep[16], added[16][8], nadded[16];
static long long leaves = 0, found = 0, fullcalls = 0, found_res = 0;

static void report(void) {
  found++;
  long long D1q = ordL / (q - 1);
  int ncl = 0; long long cl[16];
  for (int i = 0; i <= d; i++) { long long c = (w * M[i]) % D1q; int j; for (j = 0; j < ncl; j++) if (cl[j] == c) break; if (j == ncl) cl[ncl++] = c; }
  if (ncl <= d - 1) found_res++;
  if (found <= maxprint || ncl > d - 1) {
    printf("M={"); for (int i = 0; i <= d; i++) printf("%d%s", M[i], i < d ? "," : "");
    printf("} width=%lld classes_mod_D1(q)=%d\n", w * M[d], ncl); fflush(stdout);
  }
}

static int skipres = 0; static long long res_skipped = 0;
static void full_test(void) {
  fullcalls++;
  if (skipres) { /* residue-type sets (<= d-1 classes mod D1(q)) are universally uncovered by (K2)+Lemma 2.1(a) */
    long long D1q = ordL / (q - 1); int ncl = 0; long long cl[16];
    for (int i = 0; i <= d; i++) { long long c = (w * M[i]) % D1q; int j; for (j = 0; j < ncl; j++) if (cl[j] == c) break; if (j == ncl) cl[ncl++] = c; }
    if (ncl <= d - 1) { res_skipped++; return; }
  }
  for (int i = 0; i < nquick; i++) if (covered_row(M, quick[i])) return;
  for (long long i = 0; i < nreps; i++) if (covered_row(M, reps[i])) return;
  report();
}

static void dfs(int k, int prev) {
  for (int m = prev + 1; m <= W - (d - k); m++) {
    M[k] = m;
    if (k < d) {
      dep[k] = dep[k - 1]; nadded[k] = 0;
      if (!dep[k]) {
        if (bad1[m]) dep[k] = 1;
        else for (int i = 0; i < e; i++) { int b = ins(&B, V1[m][i]); if (b < 0) { dep[k] = 1; break; } added[k][nadded[k]++] = b; }
      }
      dfs(k + 1, m);
      for (int j = 0; j < nadded[k]; j++) B.piv[added[k][j]] = 0;
    } else {
      if (m < Wmin) continue;
      leaves++;
      int cov = 0;
      if (!dep[k - 1] && !bad1[m]) {
        int ad[8], na = 0; cov = 1;
        for (int i = 0; i < e; i++) { int b = ins(&B, V1[m][i]); if (b < 0) { cov = 0; break; } ad[na++] = b; }
        for (int j = 0; j < na; j++) B.piv[ad[j]] = 0;
      }
      if (!cov) full_test();
    }
  }
}

static long long gcdll(long long a, long long b) { while (b) { long long t = a % b; a = b; b = t; } return a; }

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: univ p e d w W [Wmin] [maxprint]\n"); return 1; }
  p = atoi(argv[1]); e = atoi(argv[2]); d = atoi(argv[3]); w = atoll(argv[4]); W = atoi(argv[5]);
  if (argc > 6) Wmin = atoi(argv[6]);
  if (argc > 7) maxprint = atoi(argv[7]);
  if (argc > 8) skipres = atoi(argv[8]);
  N = e * d; if (N > MAXN || (p > 2 && N > 16) || p > 7) { fprintf(stderr, "N too large\n"); return 1; }
  pw_[0] = 1; for (int i = 1; i <= N; i++) pw_[i] = pw_[i - 1] * p;
  q = 1; for (int i = 0; i < e; i++) q *= p;
  Lsize = pw_[N]; ordL = Lsize - 1; wq = ordL / (q - 1);
  ONES = 0; for (int i = 0; i < N; i++) ONES |= 1ULL << (4 * i);
  K8p = (uint64_t)(8 - p) * ONES; H8 = 8ULL * ONES;
  for (int c = 1; c < p; c++) for (int x = 1; x < p; x++) if ((c * x) % p == 1) invp[c] = x;
  build_field();
  char *vis = calloc((size_t)ordL, 1); reps = malloc(sizeof(long long) * (size_t)(ordL / N + 64)); nreps = 0;
  for (long long a = 1; a < ordL; a++) { if (vis[a]) continue; long long c = a; while (!vis[c]) { vis[c] = 1; c = (c * p) % ordL; } reps[nreps++] = a; }
  free(vis);
  nquick = 0; for (long long a = 2; a < ordL && nquick < 64; a++) if (gcdll(a, ordL) == 1) quick[nquick++] = a;
  V1 = malloc(sizeof(*V1) * (W + 1)); bad1 = calloc(W + 1, 1);
  for (int m = 0; m <= W; m++) {
    int32_t D = minus_one(alog[(w * (long long)m) % ordL]);
    if (D == 0) { bad1[m] = 1; continue; }
    for (int i = 0; i < e; i++) V1[m][i] = tovec(alog[(lg[D] + (long long)i * wq) % ordL]);
  }
  long long D1q = ordL / (q - 1);
  fprintf(stderr, "q=%lld d=%d w=%lld W=%d Wmin=%d  D1(q)=%lld  Frobenius classes of rows=%lld\n", q, d, w, W, Wmin, D1q, nreps);
  memset(&B, 0, sizeof B); dep[0] = 0; M[0] = 0;
  dfs(1, 0);
  printf("# q=%lld d=%d w=%lld W=%d Wmin=%d: leaves=%lld full_tests=%lld universally_uncovered=%lld (of which in <= d-1 residue classes mod D1(q): %lld); residue-type sets counted without row tests: %lld\n", q, d, w, W, Wmin, leaves, fullcalls, found, found_res, res_skipped);
  return 0;
}
