/* usearch: find (d+1)-sets M (0 in M, max M <= W) that are "universal" for the subfield K = GF(r^d) of GF(q^d),
 * q = r^g, gcd(g,d) = 1: for every beta in K^*, rank_Fr{beta^m} <= d-1 or the relation is balanced over the
 * classes m mod (q-1).
 * usage: usearch p f d g W [maxprint] [nthreads-slice i/n]
 * F_r = GF(p^f) built from tables; K = F_r[x]/(F), F primitive of degree d over F_r.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int p, f, d, g, r, W;
static long long q, qm1, rd, D1r;
static int addt[64][64], mult[64][64], negt[64], invt[64];
static int *kvec; /* kvec[i*d + c] = coordinate c of theta^i, i < rd-1 */
static int nreps, *reps;

static long long ipow(long long b, int e) { long long x = 1; while (e--) x *= b; return x; }

/* build F_r = GF(p^f) with elements as integers 0..r-1 (base-p digits of polynomial coefficients) */
static void build_fr(void) {
  /* find irreducible monic poly of degree f over F_p (f <= 3 suffices here) */
  int poly[8];
  if (f == 1) {
    for (int a = 0; a < p; a++) for (int b = 0; b < p; b++) { addt[a][b] = (a + b) % p; mult[a][b] = (a * b) % p; }
  } else {
    /* brute force: monic poly x^f + c_{f-1} x^{f-1} + ... + c_0 irreducible iff no roots in subfields... use exhaustive
       product test: irreducible iff not a product of lower-degree monic polys; for f<=3 test for roots (f=2,3). */
    int found = 0;
    for (int code = 0; code < ipow(p, f) && !found; code++) {
      int c = code; for (int i = 0; i < f; i++) { poly[i] = c % p; c /= p; } poly[f] = 1;
      if (poly[0] == 0) continue;
      int hasroot = 0;
      for (int x = 0; x < p; x++) { long long v = 0, xp = 1; for (int i = 0; i <= f; i++) { v += poly[i] * xp; xp = xp * x; } if (v % p == 0) hasroot = 1; }
      if (f <= 3 && !hasroot) found = 1;
    }
    if (!found) { fprintf(stderr, "no irreducible\n"); exit(1); }
    for (int a = 0; a < r; a++) for (int b = 0; b < r; b++) {
      int A[8] = {0}, B[8] = {0}, C[16] = {0}; int x = a, y = b;
      for (int i = 0; i < f; i++) { A[i] = x % p; x /= p; B[i] = y % p; y /= p; }
      int s = 0, pw = 1; for (int i = 0; i < f; i++) { s += ((A[i] + B[i]) % p) * pw; pw *= p; } addt[a][b] = s;
      for (int i = 0; i < f; i++) for (int j = 0; j < f; j++) C[i + j] = (C[i + j] + A[i] * B[j]) % p;
      for (int k = 2 * f - 2; k >= f; k--) if (C[k]) { int t = C[k]; for (int i = 0; i <= f; i++) C[k - f + i] = ((C[k - f + i] - t * poly[i]) % p + p) % p; }
      s = 0; pw = 1; for (int i = 0; i < f; i++) { s += C[i] * pw; pw *= p; } mult[a][b] = s;
    }
  }
  for (int a = 0; a < r; a++) { for (int b = 0; b < r; b++) { if (addt[a][b] == 0) negt[a] = b; if (mult[a][b] == 1) invt[a] = b; } }
}

/* K = F_r[x]/(F): find primitive F of degree d */
static void build_k(void) {
  long long N = rd - 1;
  int *F = malloc((d + 1) * sizeof(int));
  int *v = malloc(d * sizeof(int)), *w = malloc(d * sizeof(int));
  kvec = malloc(sizeof(int) * (size_t)N * d);
  long long ncodes = ipow(r, d);
  for (long long code = 0; code < ncodes; code++) {
    long long c = code; for (int i = 0; i < d; i++) { F[i] = c % r; c /= r; } F[d] = 1;
    if (F[0] == 0) continue;
    memset(v, 0, d * sizeof(int)); v[0] = 1;
    long long k;
    for (k = 0; k < N; k++) {
      memcpy(kvec + k * d, v, d * sizeof(int));
      /* v *= x */
      int top = v[d - 1];
      for (int i = d - 1; i > 0; i--) w[i] = v[i - 1]; w[0] = 0;
      if (top) for (int i = 0; i < d; i++) w[i] = addt[w[i]][negt[mult[top][F[i]]]];
      memcpy(v, w, d * sizeof(int));
      int isone = (v[0] == 1); for (int i = 1; i < d && isone; i++) if (v[i]) isone = 0;
      if (isone) { k++; break; }
    }
    if (k == N) { fprintf(stderr, "K = F_%d[x]/(", r); for (int i = d; i >= 0; i--) fprintf(stderr, "%d ", F[i]); fprintf(stderr, ")\n"); free(v); free(w); return; }
  }
  fprintf(stderr, "no primitive poly\n"); exit(1);
}


/* test universality of M[0..d] */
static int test(const long long *M, long long *failb) {
  int cls[16], ncls = 0; long long cv[16];
  for (int i = 0; i <= d; i++) { long long c = M[i] % qm1; int j; for (j = 0; j < ncls; j++) if (cv[j] == c) break; if (j == ncls) cv[ncls++] = c; cls[i] = j; }
  int mat[16][32];
  int cols = d + ncls;
  for (int t = 0; t < nreps; t++) {
    long long b = reps[t];
    for (int i = 0; i <= d; i++) {
      long long e = (b * M[i]) % (rd - 1);
      memcpy(mat[i], kvec + e * d, d * sizeof(int));
      for (int j = 0; j < ncls; j++) mat[i][d + j] = 0;
      mat[i][d + cls[i]] = 1;
    }
    /* eliminate on K columns */
    int rank = 0;
    for (int c = 0; c < d; c++) {
      int piv = -1; for (int i = rank; i <= d; i++) if (mat[i][c]) { piv = i; break; }
      if (piv < 0) continue;
      if (piv != rank) for (int k = 0; k < cols; k++) { int tt = mat[piv][k]; mat[piv][k] = mat[rank][k]; mat[rank][k] = tt; }
      int iv = invt[mat[rank][c]];
      for (int k = 0; k < cols; k++) mat[rank][k] = mult[iv][mat[rank][k]];
      for (int i = 0; i <= d; i++) if (i != rank && mat[i][c]) { int fct = mat[i][c]; for (int k = 0; k < cols; k++) mat[i][k] = addt[mat[i][k]][negt[mult[fct][mat[rank][k]]]]; }
      rank++;
    }
    if (rank <= d - 1) continue;
    /* rank == d: row d (the unique remaining row) has zero K part; balanced iff its class part is zero */
    int bal = 1; for (int k = d; k < cols; k++) if (mat[d][k]) { bal = 0; break; }
    if (bal) continue;
    if (failb) *failb = b;
    return 0;
  }
  return 1;
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: usearch p f d g W [maxprint] [slice nslices]\n"); return 1; }
  p = atoi(argv[1]); f = atoi(argv[2]); d = atoi(argv[3]); g = atoi(argv[4]); W = atoi(argv[5]);
  int maxprint = argc > 6 ? atoi(argv[6]) : 1000000;
  int slice = argc > 8 ? atoi(argv[7]) : 0, nsl = argc > 8 ? atoi(argv[8]) : 1;
  r = (int)ipow(p, f); q = ipow(r, g); qm1 = q - 1; rd = ipow(r, d); D1r = (rd - 1) / (r - 1);
  build_fr(); build_k();
  reps = malloc(sizeof(int) * D1r); char *seen = calloc(D1r, 1); nreps = 0;
  for (long long b = 0; b < D1r; b++) { if (seen[b]) continue; long long c = b; while (!seen[c]) { seen[c] = 1; c = (c * r) % D1r; } reps[nreps++] = (int)b; }
  /* order reps: put b=0 last (always passes) */
  long long D1q = (ipow(q, d) - 1) / (q - 1); long long x = D1q / D1r;
  fprintf(stderr, "r=%d q=%lld d=%d x=%lld D1r=%lld D1q=%lld W=%d reps=%d\n", r, q, d, x, D1r, D1q, W, nreps);
  long long M[16]; int idx[16];
  long long count = 0, found = 0;
  M[0] = 0;
  /* enumerate m1 < ... < md in [1, W]; slice on m1 */
  for (int i = 1; i <= d; i++) idx[i] = i;
  while (1) {
    if ((idx[1] % nsl) == slice) {
      for (int i = 1; i <= d; i++) M[i] = idx[i];
      count++;
      if (test(M, NULL)) {
        found++;
        if (found <= maxprint) {
          printf("M=");
          for (int i = 0; i <= d; i++) printf("%lld%s", M[i], i < d ? "," : "");
          printf(" max*x=%lld classes=", M[d] * x);
          for (int i = 0; i <= d; i++) printf("%lld%s", M[i] % qm1, i < d ? "," : "");
          printf("\n"); fflush(stdout);
        }
      }
    }
    int i = d; while (i >= 1 && idx[i] == W - (d - i)) i--;
    if (i < 1) break;
    idx[i]++; for (int j = i + 1; j <= d; j++) idx[j] = idx[j - 1] + 1;
  }
  fprintf(stderr, "tested=%lld found=%lld\n", count, found);
  return 0;
}
