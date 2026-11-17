/* singer.h -- PG(2,q) as the Singer group Z_N (N = q^2+q+1): point i = [alpha^i], alpha primitive in GF(q^3).
   Builds GF(q) (q = p^r <= 256) by tables, GF(q^3) from a cubic with no root in GF(q), a primitive alpha, and the
   line table: L[i*N + j] = s with i, j on line D + s, D = {i : first coordinate of alpha^i is 0}.
   collinear(i,j,k) for distinct i,j,k: (k - L[i][j]) mod N in D.  (family-theorems lane, 17 Nov 2026) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int Q, P, Rdeg, N;
static int gadd[256][256], gmul[256][256];
static int *Lt;          /* N*N line table */
static unsigned char *inD;

static int is_prime(int n) { if (n < 2) return 0; for (int d = 2; d * d <= n; d++) if (n % d == 0) return 0; return 1; }

/* GF(p^r): elements are base-p digit vectors; multiply modulo an irreducible of degree r */
static int setup_gfq(int q) {
    Q = q; P = 0;
    for (int p = 2; p <= q; p++) if (is_prime(p)) { int t = q; int r = 0; while (t % p == 0) { t /= p; r++; } if (t == 1) { P = p; Rdeg = r; break; } }
    if (!P) return 0;
    int poly[9] = {0};              /* monic irreducible of degree Rdeg: coefficients poly[0..Rdeg-1] */
    if (Rdeg == 1) {
        for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) { gadd[a][b] = (a + b) % P; gmul[a][b] = (a * b) % P; }
        return 1;
    }
    int found = 0;
    if (P == 2 && Rdeg >= 5) {                     /* fixed irreducibles over GF(2) for r = 5..10 */
        static const int IRR2[11] = {0, 0, 0, 0, 0, 0x25, 0x43, 0x83, 0x11D, 0x211, 0x409};
        for (int i = 0; i < Rdeg; i++) poly[i] = (IRR2[Rdeg] >> i) & 1;
        found = 1;
    }
    for (int c = 0; c < q && !found; c++) {        /* candidate low coefficients encoded base p */
        int t = c; for (int i = 0; i < Rdeg; i++) { poly[i] = t % P; t /= P; }
        if (poly[0] == 0) continue;
        /* irreducible iff no factor of degree <= r/2: brute force by checking x^(p^r) = x and gcd conditions is long;
           for r <= 4 test: no root, and (r == 4) no quadratic factor */
        int ok = 1;
        for (int x = 0; x < P && ok; x++) { int v = 1, s = 0; for (int i = 0; i < Rdeg; i++) { s = (s + poly[i] * v) % P; v = v * x % P; } s = (s + v) % P; if (s == 0) ok = 0; }
        if (ok && Rdeg == 4) {
            for (int a = 0; a < P && ok; a++) for (int b = 0; b < P && ok; b++) {
                /* divide x^4 + poly by x^2 + a x + b over F_p */
                int r_[5]; for (int i = 0; i < 4; i++) r_[i] = poly[i]; r_[4] = 1;
                for (int d = 4; d >= 2; d--) { int c2 = r_[d]; r_[d] = 0; r_[d - 1] = ((r_[d - 1] - c2 * a) % P + P) % P; r_[d - 2] = ((r_[d - 2] - c2 * b) % P + P) % P; }
                if (r_[0] == 0 && r_[1] == 0) ok = 0;
            }
        }
        if (ok) found = 1;
    }
    if (!found) return 0;
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int da[8], db[8], s = 0, m = 1;
        int ta = a, tb = b;
        for (int i = 0; i < Rdeg; i++) { da[i] = ta % P; ta /= P; db[i] = tb % P; tb /= P; }
        for (int i = 0; i < Rdeg; i++) { s += ((da[i] + db[i]) % P) * m; m *= P; }
        gadd[a][b] = s;
        int pr[16] = {0};
        for (int i = 0; i < Rdeg; i++) for (int j = 0; j < Rdeg; j++) pr[i + j] = (pr[i + j] + da[i] * db[j]) % P;
        for (int d = 2 * Rdeg - 2; d >= Rdeg; d--) { int c2 = pr[d]; pr[d] = 0; for (int i = 0; i < Rdeg; i++) pr[d - Rdeg + i] = ((pr[d - Rdeg + i] - c2 * poly[i]) % P + P) % P; }
        s = 0; m = 1; for (int i = 0; i < Rdeg; i++) { s += pr[i] * m; m *= P; }
        gmul[a][b] = s;
    }
    return 1;
}
static int gneg(int a) { for (int b = 0; b < Q; b++) if (gadd[a][b] == 0) return b; return -1; }

/* GF(q^3) element: v[0] + v[1] X + v[2] X^2 modulo X^3 = c2 X^2 + c1 X + c0 */
static int C0, C1, C2;
static int ALPHA[3];
static void mul3(const int *a, const int *b, int *out) {
    int pr[5] = {0, 0, 0, 0, 0};
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) pr[i + j] = gadd[pr[i + j]][gmul[a[i]][b[j]]];
    for (int d = 4; d >= 3; d--) {
        int c = pr[d]; pr[d] = 0;
        pr[d - 1] = gadd[pr[d - 1]][gmul[c][C2]];
        pr[d - 2] = gadd[pr[d - 2]][gmul[c][C1]];
        pr[d - 3] = gadd[pr[d - 3]][gmul[c][C0]];
    }
    out[0] = pr[0]; out[1] = pr[1]; out[2] = pr[2];
}

static int setup_singer(int q) {
    if (!setup_gfq(q)) return 0;
    N = q * q + q + 1;
    int found = 0;
    for (int c0 = 1; c0 < q && !found; c0++) for (int c1 = 0; c1 < q && !found; c1++) for (int c2 = 0; c2 < q && !found; c2++) {
        int ok = 1;   /* X^3 - c2 X^2 - c1 X - c0 has no root */
        for (int x = 0; x < q && ok; x++) {
            int x2 = gmul[x][x], x3 = gmul[x2][x];
            int v = gadd[gadd[gadd[x3][gneg(gmul[c2][x2])]][gneg(gmul[c1][x])]][gneg(c0)];
            if (v == 0) ok = 0;
        }
        if (!ok) continue;
        C0 = c0; C1 = c1; C2 = c2;
        /* look for a primitive element among X + t, X^2 + X + t ... : order q^3 - 1 */
        long ord = (long)q * q * q - 1;
        for (int t = 0; t < q * q && !found; t++) {
            int a[3] = {t % q, 1, t / q}; if (t >= q) { a[1] = 1; }
            int cur[3] = {1, 0, 0}, nx[3];
            long k; int prim = 1;
            for (k = 1; k <= ord; k++) {
                mul3(cur, a, nx); cur[0] = nx[0]; cur[1] = nx[1]; cur[2] = nx[2];
                if (cur[0] == 1 && cur[1] == 0 && cur[2] == 0) break;
            }
            if (k != ord) prim = 0;
            if (!prim) continue;
            /* points: alpha^i, i < N; D = {i : coordinate 0 == 0} */
            inD = calloc(N, 1);
            int v[3] = {1, 0, 0};
            for (int i = 0; i < N; i++) { if (v[0] == 0) inD[i] = 1; mul3(v, a, nx); v[0] = nx[0]; v[1] = nx[1]; v[2] = nx[2]; }
            int cnt = 0; for (int i = 0; i < N; i++) cnt += inD[i];
            if (cnt != q + 1) { free(inD); continue; }
            found = 1; ALPHA[0] = a[0]; ALPHA[1] = a[1]; ALPHA[2] = a[2];
        }
    }
    if (!found) return 0;
    int D[300], nd = 0; for (int i = 0; i < N; i++) if (inD[i]) D[nd++] = i;
    if (getenv("NO_LINE_TABLE")) { Lt = NULL; return 1; }   /* large q: callers use their own collinearity test */
    Lt = malloc((size_t)N * N * sizeof(int));
    for (size_t i = 0; i < (size_t)N * N; i++) Lt[i] = -1;
    for (int s = 0; s < N; s++) for (int x = 0; x < nd; x++) for (int y = 0; y < nd; y++) if (x != y) {
        int i = (D[x] + s) % N, j = (D[y] + s) % N;
        if (Lt[(size_t)i * N + j] != -1) { fprintf(stderr, "not a planar difference set\n"); return 0; }
        Lt[(size_t)i * N + j] = s;
    }
    return 1;
}
static inline int collinear3(int i, int j, int k) {   /* distinct points */
    int s = Lt[(size_t)i * N + j]; int d = k - s; d %= N; if (d < 0) d += N; return inD[d];
}
/* row covers three points: distinct and not collinear */
static inline int covers(int i, int j, int k) { return i != j && j != k && i != k && !collinear3(i, j, k); }
