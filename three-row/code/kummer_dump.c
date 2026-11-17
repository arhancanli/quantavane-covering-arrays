/* kummer3.c -- check Theorem K (family-theorems lane, 17 Nov 2026), written separately from singer.h / orbit3.c.
   Field: GF(q) for q = 2^r (r <= 10) from a fixed irreducible polynomial; GF(q^3) = GF(q)[b]/(b^3 - c) with c a
   NON-cube of GF(q) (exists iff 3 | q - 1). Points of PG(2,q): normalised vectors (first non-zero coordinate 1).
   Columns: base(x) = (x, x^-1, x) and extra(x) = (x, b x^-1, b x) for every point x (2N columns).
   A row covers three columns when the three entries are linearly independent over GF(q) (3x3 determinant != 0;
   this also rejects coinciding points). Invariance: multiplying rows (1,2,3) by (g, g^-1, g) maps base(x) to
   base(gx) and extra(x) to extra(gx), so only triples containing base(1) or extra(1) are tested, each such triple
   once per representative it contains (no triple is skipped).
   usage: kummer_dump r 0 OUTFILE   (writes the Theorem K array and exits)    (q = 2^r; sabotage = 1 uses b x instead of b x^-1 in row 2: a red control) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int Q, R;
static uint16_t LOG[1024], EXP[2048];
static const int IRR[11] = {0, 0, 0x7, 0xB, 0x13, 0x25, 0x43, 0x83, 0x11D, 0x211, 0x409};   /* x^r + ... over GF(2) */
static inline int fmul(int a, int b) { if (!a || !b) return 0; return EXP[LOG[a] + LOG[b]]; }
static inline int finv(int a) { return EXP[(Q - 1 - LOG[a]) % (Q - 1)]; }
static int C;                      /* b^3 = C */
typedef struct { int a[3]; } E;    /* a0 + a1 b + a2 b^2 */
static E emul(E x, E y) {
    int p[5] = {0, 0, 0, 0, 0};
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) p[i + j] ^= fmul(x.a[i], y.a[j]);
    E z; z.a[0] = p[0] ^ fmul(p[3], C); z.a[1] = p[1] ^ fmul(p[4], C); z.a[2] = p[2]; return z;
}
static E epow(E x, long long e) { E r = {{1, 0, 0}}; while (e) { if (e & 1) r = emul(r, x); x = emul(x, x); e >>= 1; } return r; }
static E norm(E x) {   /* scale so the first non-zero coordinate is 1 */
    int k = x.a[0] ? 0 : (x.a[1] ? 1 : 2); int s = finv(x.a[k]);
    E z; for (int i = 0; i < 3; i++) z.a[i] = fmul(x.a[i], s); return z;
}
static int det3(const E *u, const E *v, const E *w) {
    int d = 0;
    d ^= fmul(u->a[0], fmul(v->a[1], w->a[2]) ^ fmul(v->a[2], w->a[1]));
    d ^= fmul(u->a[1], fmul(v->a[0], w->a[2]) ^ fmul(v->a[2], w->a[0]));
    d ^= fmul(u->a[2], fmul(v->a[0], w->a[1]) ^ fmul(v->a[1], w->a[0]));
    return d;
}
int main(int argc, char **argv) {
    R = atoi(argv[1]); int sab = argc > 2 ? atoi(argv[2]) : 0; Q = 1 << R;
    if (R < 2 || R > 10) return 2;
    int x = 1; for (int i = 0; i < Q - 1; i++) { EXP[i] = x; LOG[x] = i; x <<= 1; if (x & Q) x ^= IRR[R]; }
    for (int i = Q - 1; i < 2 * Q; i++) EXP[i] = EXP[i - (Q - 1)];
    { int seen = 0; for (int i = 1; i < Q; i++) if (LOG[i] == 0 && i != 1) seen = 1; if (seen) { fprintf(stderr, "x not primitive\n"); return 2; } }
    if ((Q - 1) % 3) { printf("q = %d: 3 does not divide q - 1, no Kummer cube\n", Q); return 1; }
    C = EXP[1];                                   /* the generator: a non-cube since 3 | q - 1 */
    long long q3 = (long long)Q * Q * Q;
    int N = Q * Q + Q + 1;
    E *P = malloc(sizeof(E) * N); int np = 0;
    for (int a1 = 0; a1 < Q; a1++) for (int a2 = 0; a2 < Q; a2++) { E e = {{1, a1, a2}}; P[np++] = e; }
    for (int a2 = 0; a2 < Q; a2++) { E e = {{0, 1, a2}}; P[np++] = e; }
    { E e = {{0, 0, 1}}; P[np++] = e; }
    if (np != N) return 2;
    E bb = {{0, 1, 0}};
    /* columns: 0..N-1 base, N..2N-1 extra; rows stored normalised */
    E (*col)[3] = malloc(sizeof(E[3]) * 2 * N);
    for (int i = 0; i < N; i++) {
        E xi = P[i], inv = epow(xi, q3 - 2);
        col[i][0] = xi; col[i][1] = norm(inv); col[i][2] = xi;
        col[N + i][0] = xi; col[N + i][1] = norm(emul(bb, sab ? xi : inv)); col[N + i][2] = norm(emul(bb, xi));
    }
    /* dump: one column per line, three entries "a0,a1,a2" = coordinates in the basis (1, b, b^2); GF(2^r) elements
       as integers whose bit i is the coefficient of x^i, modulo the polynomial IRR[r] */
    if (argc > 3) { FILE *o = fopen(argv[3], "w"); for (int c = 0; c < 2 * N; c++) { for (int t = 0; t < 3; t++)
        fprintf(o, "%d,%d,%d%c", col[c][t].a[0], col[c][t].a[1], col[c][t].a[2], t < 2 ? ' ' : '\n'); } fclose(o);
        fprintf(stderr, "dumped %d columns; b^3 = %d; polynomial 0x%X\n", 2 * N, C, IRR[R]); return 0; }
    /* sanity: b^3 = C */
    E b3 = epow(bb, 3); if (!(b3.a[0] == C && b3.a[1] == 0 && b3.a[2] == 0)) { fprintf(stderr, "b^3 != C\n"); return 2; }
    long long tested = 0, bad = 0; int K = 2 * N;
    int reps[2] = {0, N};     /* base(1) and extra(1): P[0] = (1,0,0) = the field element 1 */
    for (int r = 0; r < 2; r++) { int c0 = reps[r];
        for (int i = 0; i < K; i++) { if (i == c0) continue;
            for (int j = i + 1; j < K; j++) { if (j == c0) continue;
                tested++;
                int ok = 0;
                for (int t = 0; t < 3 && !ok; t++) if (det3(&col[c0][t], &col[i][t], &col[j][t])) ok = 1;
                if (!ok) { if (bad < 5) printf("UNCOVERED: %d %d %d\n", c0, i, j); bad++; }
            } } }
    printf("q %d N %d k %d triples tested %lld uncovered %lld -> %s\n", Q, N, K, tested, bad, bad ? "FAIL" : "PASS: CPHF(3; 2N, q, 3)");
    return bad ? 1 : 0;
}
