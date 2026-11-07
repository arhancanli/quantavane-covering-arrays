/* usearch2: the search of usearch.c (same criterion, Theorem 4.3(b)), organized by the largest element of M and
 * accelerated by solving for one element of M instead of enumerating it.
 *
 * M = {0 < m_1 < ... < m_d}, m_d = W' runs from d to W. For a prefix P = M minus one element m (the second largest,
 * m_{d-1}), take the first beta in the list of representatives for which the d elements beta^p (p in P) are
 * linearly independent over F_r (a basis of K). For any m, the d+1 elements beta^M then span K, so
 * R(beta, M) = F_r rho with rho = (coordinates of beta^m in that basis, -1), and the criterion for this beta holds
 * iff rho is balanced: the class of m must be one of the classes C' of P, and the coordinates c(beta^m) must have
 * sum 1 over the members of P in C' and sum 0 over the members of every other class of P. That is an affine
 * condition T(beta^m) = e_{C'} on beta^m, T : K -> F_r^s (s = number of classes of P) linear of rank s; its solution
 * set has r^(d-s) elements, and for each we look up m = log_theta(z) (z = theta^m exactly, m mod r^d - 1). Every
 * m in (m_{d-2}, W') found this way, with m in class C', is then tested in full against every representative beta
 * (function test, as in usearch.c). If P is dependent for every representative, every m is tested in full.
 * The result is exactly the list of usearch.c (checked on the cases in run_subfield.sh).
 * Progress: a line "done max W'" after each W', so a partial run decides every M with max M <= the last W'.
 * usage: usearch2 p f d g W [Wstart] [slice nslices]     (slices split the values of W')
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int p, f, d, g, r, W;
static long long q, qm1, rd, D1r;
static int addt[64][64], mult[64][64], negt[64], invt[64];
static int *kvec;      /* kvec[i*d + c]: coordinate c of theta^i */
static int *logt;      /* logt[code of z] = i with theta^i = z (z != 0) */
static int nreps, *reps;

static long long ipow(long long b, int e) { long long x = 1; while (e--) x *= b; return x; }

static void build_fr(void) {
  int poly[8];
  if (f == 1) {
    for (int a = 0; a < p; a++) for (int b = 0; b < p; b++) { addt[a][b] = (a + b) % p; mult[a][b] = (a * b) % p; }
  } else {
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
  for (int a = 0; a < r; a++) for (int b = 0; b < r; b++) { if (addt[a][b] == 0) negt[a] = b; if (mult[a][b] == 1) invt[a] = b; }
}

static void build_k(void) {
  long long N = rd - 1;
  int *F = malloc((d + 1) * sizeof(int)), *v = malloc(d * sizeof(int)), *w = malloc(d * sizeof(int));
  kvec = malloc(sizeof(int) * (size_t)N * d);
  for (long long code = 0; code < ipow(r, d); code++) {
    long long c = code; for (int i = 0; i < d; i++) { F[i] = c % r; c /= r; } F[d] = 1;
    if (F[0] == 0) continue;
    memset(v, 0, d * sizeof(int)); v[0] = 1;
    long long k;
    for (k = 0; k < N; k++) {
      memcpy(kvec + k * d, v, d * sizeof(int));
      int top = v[d - 1];
      for (int i = d - 1; i > 0; i--) w[i] = v[i - 1]; w[0] = 0;
      if (top) for (int i = 0; i < d; i++) w[i] = addt[w[i]][negt[mult[top][F[i]]]];
      memcpy(v, w, d * sizeof(int));
      int isone = (v[0] == 1); for (int i = 1; i < d && isone; i++) if (v[i]) isone = 0;
      if (isone) { k++; break; }
    }
    if (k == N) {
      fprintf(stderr, "K = F_%d[x]/(", r); for (int i = d; i >= 0; i--) fprintf(stderr, "%d ", F[i]); fprintf(stderr, ")\n");
      logt = malloc(sizeof(int) * (size_t)rd);
      for (long long i = 0; i < rd; i++) logt[i] = -1;
      for (long long i = 0; i < N; i++) { long long code2 = 0; for (int j = d - 1; j >= 0; j--) code2 = code2 * r + kvec[i * d + j]; logt[code2] = (int)i; }
      return;
    }
  }
  fprintf(stderr, "no primitive poly\n"); exit(1);
}

/* full test of M[0..d] (as usearch.c) */
static int test(const long long *M) {
  int cls[16], ncls = 0; long long cv[16];
  for (int i = 0; i <= d; i++) { long long c = M[i] % qm1; int j; for (j = 0; j < ncls; j++) if (cv[j] == c) break; if (j == ncls) cv[ncls++] = c; cls[i] = j; }
  int mat[16][32]; int cols = d + ncls;
  for (int t = 0; t < nreps; t++) {
    long long b = reps[t];
    for (int i = 0; i <= d; i++) {
      long long e = (b * M[i]) % (rd - 1);
      memcpy(mat[i], kvec + e * d, d * sizeof(int));
      for (int j = 0; j < ncls; j++) mat[i][d + j] = 0;
      mat[i][d + cls[i]] = 1;
    }
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
    int bal = 1; for (int k = d; k < cols; k++) if (mat[d][k]) { bal = 0; break; }
    if (bal) continue;
    return 0;
  }
  return 1;
}

static long long found = 0, fulltests = 0, prefixes = 0, fallback = 0;
static long long xw;

static void report(long long *M) {
  long long S[16]; for (int i = 0; i <= d; i++) S[i] = M[i];
  for (int i = 1; i <= d; i++) for (int j = i; j > 0 && S[j - 1] > S[j]; j--) { long long t = S[j]; S[j] = S[j - 1]; S[j - 1] = t; }
  found++;
  printf("M=");
  for (int i = 0; i <= d; i++) printf("%lld%s", S[i], i < d ? "," : "");
  printf(" max*w=%lld classes=", S[d] * xw);
  for (int i = 0; i <= d; i++) printf("%lld%s", S[i] % qm1, i < d ? "," : "");
  printf("\n"); fflush(stdout);
}

/* prefix P[0..d-1] (P[d-1] = W' the maximum, P[d-2] = m_{d-2}); the free element m lies in (lo, hi) */
static void handle_prefix(long long *P, long long lo, long long hi) {
  prefixes++;
  int s = 0; long long cv[16]; int cls[16];
  for (int i = 0; i < d; i++) { long long c = P[i] % qm1; int j; for (j = 0; j < s; j++) if (cv[j] == c) break; if (j == s) cv[s++] = c; cls[i] = j; }
  /* find a representative beta with beta^P a basis; compute the inverse matrix */
  int V[16][16], Inv[16][16];
  int bsel = -1;
  for (int t = 0; t < nreps && bsel < 0; t++) {
    long long b = reps[t];
    int A[16][32];
    for (int i = 0; i < d; i++) {
      long long e = (b * P[i]) % (rd - 1);
      for (int c = 0; c < d; c++) { A[i][c] = kvec[e * d + c]; V[i][c] = A[i][c]; }
      for (int c = 0; c < d; c++) A[i][d + c] = (i == c);
    }
    int ok = 1;
    for (int c = 0; c < d; c++) {
      int piv = -1; for (int i = c; i < d; i++) if (A[i][c]) { piv = i; break; }
      if (piv < 0) { ok = 0; break; }
      if (piv != c) for (int k = 0; k < 2 * d; k++) { int tt = A[piv][k]; A[piv][k] = A[c][k]; A[c][k] = tt; }
      int iv = invt[A[c][c]];
      for (int k = 0; k < 2 * d; k++) A[c][k] = mult[iv][A[c][k]];
      for (int i = 0; i < d; i++) if (i != c && A[i][c]) { int fct = A[i][c]; for (int k = 0; k < 2 * d; k++) A[i][k] = addt[A[i][k]][negt[mult[fct][A[c][k]]]]; }
    }
    if (!ok) continue;
    /* A[:, d..2d-1] = V^{-1} (row-vector convention: z = c V  <=>  c = z V^{-1}) */
    for (int i = 0; i < d; i++) for (int c = 0; c < d; c++) Inv[i][c] = A[i][d + c];
    bsel = (int)b;
  }
  long long M[16];
  for (int i = 0; i < d; i++) M[i] = P[i];
  if (bsel < 0) {
    /* dependent for every representative: test every m */
    fallback++;
    for (long long m = lo + 1; m < hi; m++) { M[d] = m; fulltests++; if (test(M)) report(M); }
    return;
  }
  /* T(z)_C = sum_{i: cls[i]=C} (z Inv)_i : a d x s matrix Tm[c][C] = sum_{i in C} Inv[c][i] */
  int Tm[16][16];
  for (int c = 0; c < d; c++) for (int C = 0; C < s; C++) { int acc = 0; for (int i = 0; i < d; i++) if (cls[i] == C) acc = addt[acc][Inv[c][i]]; Tm[c][C] = acc; }
  /* solve z Tm = e_{C'} for each C': row-reduce the s x (d + s) system Tm^T | I  */
  /* Build augmented matrix G (s rows, d columns) = Tm^T; we need all z (row vectors of length d) with z Tm = target.
     Equivalently Tm^T z^T = target^T. Reduce [Tm^T | target] for all targets at once via [Tm^T | I_s]. */
  int G[16][32]; int nc = d + s;
  for (int C = 0; C < s; C++) { for (int c = 0; c < d; c++) G[C][c] = Tm[c][C]; for (int C2 = 0; C2 < s; C2++) G[C][d + C2] = (C == C2); }
  int pivcol[16], rank = 0;
  for (int c = 0; c < d && rank < s; c++) {
    int piv = -1; for (int i = rank; i < s; i++) if (G[i][c]) { piv = i; break; }
    if (piv < 0) continue;
    if (piv != rank) for (int k = 0; k < nc; k++) { int tt = G[piv][k]; G[piv][k] = G[rank][k]; G[rank][k] = tt; }
    int iv = invt[G[rank][c]];
    for (int k = 0; k < nc; k++) G[rank][k] = mult[iv][G[rank][k]];
    for (int i = 0; i < s; i++) if (i != rank && G[i][c]) { int fct = G[i][c]; for (int k = 0; k < nc; k++) G[i][k] = addt[G[i][k]][negt[mult[fct][G[rank][k]]]]; }
    pivcol[rank++] = c;
  }
  if (rank != s) { fprintf(stderr, "T not of full rank\n"); exit(2); }
  int isfree[16] = {0}; for (int c = 0; c < d; c++) isfree[c] = 1; for (int i = 0; i < s; i++) isfree[pivcol[i]] = 0;
  int frees[16], nf = 0; for (int c = 0; c < d; c++) if (isfree[c]) frees[nf++] = c;
  long long ncomb = ipow(r, nf);
  long long N1 = rd - 1, g0 = N1, bb = bsel; { long long a0 = bb, b0 = N1; while (b0) { long long t0 = a0 % b0; a0 = b0; b0 = t0; } g0 = a0; }
  long long mod0 = N1 / g0, inv0 = 1;
  { /* inverse of (bsel/g0) modulo mod0 */
    long long a0 = (bb / g0) % mod0, m1 = mod0, x0 = 1, x1 = 0;
    if (mod0 == 1) inv0 = 0; else { long long aa = a0, mm = m1; while (mm) { long long qq = aa / mm, t0 = aa - qq * mm; aa = mm; mm = t0; t0 = x0 - qq * x1; x0 = x1; x1 = t0; } inv0 = ((x0 % mod0) + mod0) % mod0; }
  }
  int z[16];
  for (int Ct = 0; Ct < s; Ct++) {
    for (long long code = 0; code < ncomb; code++) {
      long long cc = code;
      for (int j = 0; j < nf; j++) { z[frees[j]] = (int)(cc % r); cc /= r; }
      /* pivot variables: z[pivcol[i]] = G[i][d + Ct] - sum_{free j} G[i][frees[j]] z[frees[j]] */
      for (int i = 0; i < s; i++) {
        int acc = G[i][d + Ct];
        for (int j = 0; j < nf; j++) acc = addt[acc][negt[mult[G[i][frees[j]]][z[frees[j]]]]];
        z[pivcol[i]] = acc;
      }
      long long code2 = 0; int nz = 0;
      for (int j = d - 1; j >= 0; j--) { code2 = code2 * r + z[j]; if (z[j]) nz = 1; }
      if (!nz) continue;
      long long e = logt[code2];          /* theta^e = z; beta^m = z with beta = theta^bsel: m bsel = e mod rd-1 */
      /* all m in (lo, hi) with bsel*m = e (mod rd-1) and m = cv[Ct] (mod q-1) */
      if (e % g0) continue;
      long long m0 = ((e / g0) % mod0) * inv0 % mod0;
      long long m = m0 + ((lo + 1 - m0 + mod0 - 1) / mod0) * mod0;  /* least m >= lo + 1 with m = m0 mod mod0 */
      if (m0 >= lo + 1) m = m0 - ((m0 - (lo + 1)) / mod0) * mod0;
      for (; m < hi; m += mod0) {
        if (m <= lo) continue;
        if ((m % qm1) != cv[Ct]) continue;
        M[d] = m; fulltests++;
        if (test(M)) report(M);
      }
    }
  }
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: usearch2 p f d g W [Wstart] [slice nslices]\n"); return 1; }
  p = atoi(argv[1]); f = atoi(argv[2]); d = atoi(argv[3]); g = atoi(argv[4]); W = atoi(argv[5]);
  int Wstart = argc > 6 ? atoi(argv[6]) : d;
  int slice = argc > 8 ? atoi(argv[7]) : 0, nsl = argc > 8 ? atoi(argv[8]) : 1;
  r = (int)ipow(p, f); q = ipow(r, g); qm1 = q - 1; rd = ipow(r, d); D1r = (rd - 1) / (r - 1);
  build_fr(); build_k();
  reps = malloc(sizeof(int) * D1r); char *seen = calloc(D1r, 1); nreps = 0;
  int prim = getenv("PRIM") && atoi(getenv("PRIM"));   /* PRIM=1: only classes of primitive elements (gcd(b, D1r) = 1) */
  for (long long b = 1; b < D1r; b++) {
    if (seen[b]) continue; long long c = b; while (!seen[c]) { seen[c] = 1; c = (c * r) % D1r; }
    if (prim) { long long a0 = b, b0 = D1r; while (b0) { long long t0 = a0 % b0; a0 = b0; b0 = t0; } if (a0 != 1) continue; }
    reps[nreps++] = (int)b;
  }
  if (prim) fprintf(stderr, "PRIM=1: representatives restricted to classes of primitive elements\n");
  /* b = 0 (beta in F_r^*) always satisfies the criterion and is omitted */
  long long D1q = (ipow(q, d) - 1) / (q - 1); xw = D1q / D1r;
  fprintf(stderr, "r=%d q=%lld d=%d w=%lld D1r=%lld D1q=%lld W=%d reps=%d (beta in F_r omitted)\n", r, q, d, xw, D1r, D1q, W, nreps);
  /* M = {0 < m_1 < ... < m_{d-2} < m < W'}; prefix P = {0, m_1..m_{d-2}, W'} */
  long long P[16]; int idx[16];
  for (int Wp = Wstart; Wp <= W; Wp++) {
    if ((Wp % nsl) != slice) continue;
    /* choose m_1 < ... < m_{d-2} from [1, Wp-2] */
    int kk = d - 2;
    for (int i = 1; i <= kk; i++) idx[i] = i;
    if (kk >= 1 && idx[kk] > Wp - 2) { printf("done max %d\n", Wp); fflush(stdout); continue; }
    while (1) {
      P[0] = 0; for (int i = 1; i <= kk; i++) P[i] = idx[i]; P[d - 1] = Wp;
      long long lo = kk >= 1 ? idx[kk] : 0;
      if (lo + 1 < Wp) handle_prefix(P, lo, Wp);
      int i = kk; while (i >= 1 && idx[i] == (Wp - 2) - (kk - i)) i--;
      if (i < 1) break;
      idx[i]++; for (int j = i + 1; j <= kk; j++) idx[j] = idx[j - 1] + 1;
    }
    printf("done max %d\n", Wp); fflush(stdout);
  }
  fprintf(stderr, "prefixes=%lld fulltests=%lld fallback_prefixes=%lld found=%lld\n", prefixes, fulltests, fallback, found);
  return 0;
}
