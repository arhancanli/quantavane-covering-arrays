/* pq_scphf3_bigcheck: exact check of a strength-3 Sherwood CPHF with up to a few hundred thousand columns (3 Nov 2026).
   Written apart from the searches (engine/native/cphf3*.c, pq_cphf3big.c): its own field arithmetic, its own lines,
   its own partition code, and a determinant test of every triple it reports.

   Claim checked: every three columns a < b < c hold, in some row, three points of AG(2,q) that are distinct and not
   on one line (det [[1,xa,ya],[1,xb,yb],[1,xc,yc]] != 0).
   Method, per column c (the largest of the triple): in row r every earlier column a is labelled by the line through
   c's point and a's point (the normalized cross product of (1, xc, yc) and (1, xa, ya) in PG(2,q), numbered among the
   q + 1 lines through c's point), or STAR when a stands on c's point. Row r covers {a, b, c} exactly when a and b
   have different labels and neither is STAR (then the three points are distinct, and a, b lie on different lines
   through c). So {a, b, c} is uncovered iff the labels of a and b agree in every row, STAR agreeing with anything.
   The earlier columns are split row by row, depth first, into classes of equal labels (a STAR column goes into
   every class of its group); a class of at most SMALL columns is finished pair by pair on the remaining rows. Every
   pair left at the end is tested again with the determinant over all rows (own arithmetic) before it is counted, and
   reported pairs are de-duplicated (a STAR column can meet the same partner in several classes). All C(k,3) triples
   are decided, none sampled. Cost about C(k,2) x n label lookups plus the classes' copies.
   Second, as independent/scphf_check.c: SAMPLES random column triples of the covering array it gives,
   CA(n(q^3 - q) + q; 3, k, q), must each show all q^3 tuples (row (u0,u1,u2) of block r puts u0 + u1 x + u2 y in a
   column whose point in row r is (x, y); the q constant rows once).
   Field: GF(q) for q prime, or GF(p^m) with the polynomials of the release (base-p digit vectors, digit i the
   coefficient of x^i; q 4: x^2+x+1, 8: x^3+x+1, 16: x^4+x+1, 9: x^2+1, 25: x^2+x+2, 27: x^3+2x+1, 32: x^5+x^2+1),
   multiplication by shift-and-add, every field axiom tested before use, inverses from a generator's powers.
   Input: lines that start with a digit, except "best ...", are the n rows of k point ids x*q + y.
   Shards: only triples whose largest column c lies in [FROM, TO) are checked (default all); shard outputs add up.
   PQ_CERT=1 reads a ca-tools certificate instead (lines of base-q integers, each the vector (1, x, y): q^2 + x q + y;
   '#' lines skipped), and PQ_FIELDPOLY="f0,f1,..." replaces the field polynomial (ca-tools' Conway polynomials:
   q 9 "2,2", q 25 "2,4"; the other q agree with the release), so the converted file itself is checked exactly.

   cc -O3 -march=native -o pq_scphf3_bigcheck pq_scphf3_bigcheck.c
   pq_scphf3_bigcheck q FILE [SAMPLES] [FROM TO] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 32
#define MAXN 32
#define SMALL 10

static int q, p, m, poly[8];
static int ADD[MAXQ][MAXQ], NEG[MAXQ], MUL[MAXQ][MAXQ], INV[MAXQ];

static int dig(int a, int i) { for (; i > 0; i--) a /= p; return a % p; }
static int vadd(int a, int b) {
    int r = 0, pw = 1;
    for (int i = 0; i < m; i++, pw *= p) r += ((dig(a, i) + dig(b, i)) % p) * pw;
    return r;
}
static int shift(int a) {  /* a * x modulo the polynomial: x^m = -(poly[0] + poly[1] x + ... ) */
    int top = dig(a, m - 1), r = 0, pw = 1;
    for (int i = 0; i < m; i++, pw *= p) {
        int below = i ? dig(a, i - 1) : 0;
        r += (((below - top * poly[i]) % p + p) % p) * pw;
    }
    return r;
}
static int fmul(int a, int b) {  /* sum over the digits of b of b_i * (a x^i) */
    int r = 0, ax = a;
    for (int i = 0; i < m; i++) {
        for (int t = 0; t < dig(b, i); t++) r = vadd(r, ax);
        ax = shift(ax);
    }
    return r;
}

static int build_field(void) {
    static const struct { int q, p, m, f[6]; } T[] = {  /* low degree first, without the leading 1 */
        {4, 2, 2, {1, 1}}, {8, 2, 3, {1, 1, 0}}, {16, 2, 4, {1, 1, 0, 0}}, {32, 2, 5, {1, 0, 1, 0, 0}},
        {9, 3, 2, {1, 0}}, {27, 3, 3, {1, 2, 0}}, {25, 5, 2, {2, 1}}};
    p = 0;
    for (unsigned i = 0; i < sizeof T / sizeof T[0]; i++)
        if (T[i].q == q) { p = T[i].p; m = T[i].m; memcpy(poly, T[i].f, sizeof T[i].f); }
    if (!p) {
        for (int d = 2; d * d <= q; d++) if (q % d == 0) return 0;
        p = q; m = 1; poly[0] = 0;
    }
    const char *fp = getenv("PQ_FIELDPOLY");  /* other coefficients f0,f1,... (x^m = -(f0 + f1 x + ...)), e.g. the
                                                 Conway polynomials of ca-tools: q 9 "2,2", q 25 "2,4" */
    if (fp && m > 1) {
        int i = 0;
        for (const char *s = fp; *s && i < m; i++) { poly[i] = atoi(s); while (*s && *s != ',') s++; if (*s) s++; }
        if (i != m) return 0;
        fprintf(stderr, "field polynomial coefficients from PQ_FIELDPOLY: %s\n", fp);
    }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            if (m == 1) { ADD[a][b] = (a + b) % q; MUL[a][b] = a * b % q; }
            else { ADD[a][b] = vadd(a, b); MUL[a][b] = fmul(a, b); }
        }
    for (int a = 0; a < q; a++) { NEG[a] = -1; for (int b = 0; b < q; b++) if (ADD[a][b] == 0) NEG[a] = b; if (NEG[a] < 0) return 0; }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            if (ADD[a][b] != ADD[b][a] || MUL[a][b] != MUL[b][a]) return 0;
            for (int c = 0; c < q; c++)
                if (ADD[ADD[a][b]][c] != ADD[a][ADD[b][c]] || MUL[MUL[a][b]][c] != MUL[a][MUL[b][c]] ||
                    MUL[a][ADD[b][c]] != ADD[MUL[a][b]][MUL[a][c]]) return 0;
        }
    for (int a = 0; a < q; a++) if (ADD[0][a] != a || MUL[1][a] != a || MUL[0][a] != 0) return 0;
    /* a generator: its powers run through every nonzero element; inverses from them */
    int g = -1;
    for (int c = 2; c < q + 2 && g < 0; c++) {
        int cand = c % q, x = 1, ord = 0;
        if (!cand) continue;
        do { x = MUL[x][cand]; ord++; } while (x != 1 && ord <= q);
        if (ord == q - 1) g = cand;
    }
    if (q == 2) g = 1;
    if (g < 0) return 0;
    int pw[MAXQ], lg[MAXQ];
    for (int e = 0, x = 1; e < q - 1; e++, x = MUL[x][g]) { pw[e] = x; lg[x] = e; }
    INV[0] = 0;
    for (int a = 1; a < q; a++) { INV[a] = pw[(q - 1 - lg[a]) % (q - 1)]; if (MUL[a][INV[a]] != 1) return 0; }
    return 1;
}
#define SUB(a, b) ADD[a][NEG[b]]

/* LBL[c * P + a]: label of point a seen from point c: 0..q (the line through both, numbered among the lines
   through c by its normalized coordinates), STAR if a == c */
static int P, STAR;
static uint8_t *LBL;
static void build_labels(void) {
    LBL = malloc((size_t)P * P);
    for (int c = 0; c < P; c++) {
        int xc = c / q, yc = c % q, nseen = 0;
        int key[MAXQ + 2];
        for (int a = 0; a < P; a++) {
            if (a == c) { LBL[c * P + a] = (uint8_t)STAR; continue; }
            int xa = a / q, ya = a % q;
            /* (1, xc, yc) x (1, xa, ya) = (xc ya - yc xa, yc - ya, xa - xc) */
            int u = SUB(MUL[xc][ya], MUL[yc][xa]), v = SUB(yc, ya), w = SUB(xa, xc);
            int s = v ? INV[v] : INV[w];  /* v, w not both 0 since a != c; scale the first nonzero of (v, w) to 1 */
            u = MUL[u][s]; v = MUL[v][s]; w = MUL[w][s];
            int kk = (u * q + v) * q + w, id = -1;
            for (int i = 0; i < nseen; i++) if (key[i] == kk) id = i;
            if (id < 0) { if (nseen > q) { fprintf(stderr, "more than q+1 lines through a point\n"); exit(2); } key[nseen] = kk; id = nseen++; }
            LBL[c * P + a] = (uint8_t)id;
        }
        if (nseen != q + 1) { fprintf(stderr, "point %d: %d lines, not q+1\n", c, nseen); exit(2); }
    }
}

static int n, k;
static uint16_t *Hp[MAXN];
static uint8_t *X[MAXN], *Y[MAXN];
static int cc;                 /* the current third column */
static const uint8_t *base[MAXN];

static int uncovered_det(int a, int b, int c) {  /* 1 if no row holds a triangle */
    for (int r = 0; r < n; r++) {
        int d = SUB(MUL[SUB(X[r][b], X[r][a])][SUB(Y[r][c], Y[r][a])], MUL[SUB(Y[r][b], Y[r][a])][SUB(X[r][c], X[r][a])]);
        if (d) return 0;
    }
    return 1;
}

/* reported pairs for the current c, de-duplicated */
static uint64_t *HS; static long HCAP, HN; static long *HUSED; static long HNU;
static long long bad, falsealarm;
static int fa = -1, fb = -1, fc = -1;
static void report(int a, int b) {
    if (a > b) { int t = a; a = b; b = t; }
    uint64_t key = ((uint64_t)a << 32 | (uint64_t)b) + 1;
    if (HN * 2 >= HCAP) {  /* grow: rehash */
        long oc = HCAP; uint64_t *old = HS;
        HCAP = HCAP ? HCAP * 4 : 1024;
        HS = calloc((size_t)HCAP, sizeof(uint64_t)); HUSED = realloc(HUSED, sizeof(long) * HCAP); HN = 0; HNU = 0;
        for (long i = 0; i < oc; i++) if (old[i]) {
            long h = (long)((old[i] * 0x9E3779B97F4A7C15ULL) >> 20) & (HCAP - 1);
            while (HS[h]) h = (h + 1) & (HCAP - 1);
            HS[h] = old[i]; HUSED[HNU++] = h; HN++;
        }
        free(old);
    }
    long h = (long)((key * 0x9E3779B97F4A7C15ULL) >> 20) & (HCAP - 1);
    while (HS[h]) { if (HS[h] == key) return; h = (h + 1) & (HCAP - 1); }
    HS[h] = key; HUSED[HNU++] = h; HN++;
    if (!uncovered_det(a, b, cc)) { falsealarm++; return; }
    if (!bad) { fa = a; fb = b; fc = cc; }
    bad++;
}
static void clear_reports(void) { for (long i = 0; i < HNU; i++) HS[HUSED[i]] = 0; HNU = 0; HN = 0; }

static int *BUF[MAXN + 1]; static long BCAP[MAXN + 1];
static long long work;

static void group(int r, const int *mem, int s) {
    if (s < 2) return;
    if (r == n) {  /* agree on every row */
        for (int i = 0; i < s; i++) for (int j = i + 1; j < s; j++) report(mem[i], mem[j]);
        return;
    }
    if (s <= SMALL) {
        for (int i = 0; i < s; i++)
            for (int j = i + 1; j < s; j++) {
                int a = mem[i], b = mem[j], t = r;
                for (; t < n; t++) {
                    int la = base[t][Hp[t][a]], lb = base[t][Hp[t][b]];
                    work++;
                    if (la != lb && la != STAR && lb != STAR) break;
                }
                if (t == n) report(a, b);
            }
        return;
    }
    const uint8_t *bs = base[r];
    const uint16_t *hr = Hp[r];
    int cnt[MAXQ + 2] = {0};
    for (int i = 0; i < s; i++) cnt[bs[hr[mem[i]]]]++;
    work += s;
    int ns = cnt[STAR], any = 0;
    long need = 0, start[MAXQ + 1];
    for (int d = 0; d < STAR; d++) {
        if (cnt[d]) any = 1;
        start[d] = need;
        if (cnt[d] && cnt[d] + ns >= 2) need += cnt[d] + ns; else start[d] = -1;
    }
    if (!any) {  /* every member stands on c's point in this row: the row covers none of their pairs */
        group(r + 1, mem, s);
        return;
    }
    if (need > BCAP[r]) { BCAP[r] = need * 2; BUF[r] = realloc(BUF[r], sizeof(int) * BCAP[r]); }
    int *out = BUF[r];
    long fill[MAXQ + 1];
    for (int d = 0; d < STAR; d++) fill[d] = start[d];
    for (int i = 0; i < s; i++) {
        int a = mem[i], l = bs[hr[a]];
        if (l != STAR) { if (start[l] >= 0) out[fill[l]++] = a; }
        else for (int d = 0; d < STAR; d++) if (start[d] >= 0) out[fill[d]++] = a;
    }
    for (int d = 0; d < STAR; d++) if (start[d] >= 0) group(r + 1, out + start[d], cnt[d] + ns);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: pq_scphf3_bigcheck q FILE [SAMPLES] [FROM TO]\n"); return 2; }
    q = atoi(argv[1]);
    long samples = argc > 3 ? atol(argv[3]) : 2000;
    if (q < 2 || q > MAXQ || !build_field()) { fprintf(stderr, "q is not a supported field order\n"); return 2; }
    P = q * q; STAR = q + 1;
    build_labels();
    int cert = getenv("PQ_CERT") && atoi(getenv("PQ_CERT"));  /* read a ca-tools family file (affine, base q) */
    FILE *f = fopen(argv[2], "r");
    if (!f) { perror(argv[2]); return 2; }
    size_t cap = 1 << 22;
    char *line = malloc(cap);
    k = -1; n = 0;
    while (1) {  /* lines of any length */
        size_t len = 0;
        int ch;
        while ((ch = getc(f)) != EOF && ch != '\n') { if (len + 2 >= cap) { cap *= 2; line = realloc(line, cap); } line[len++] = (char)ch; }
        if (ch == EOF && !len) break;
        line[len] = 0;
        if (line[0] < '0' || line[0] > '9') { if (ch == EOF) break; continue; }
        if (n == MAXN) { fprintf(stderr, "too many rows\n"); return 2; }
        long kc = 0, kcap = 1 << 16;
        uint16_t *row = malloc(sizeof(uint16_t) * kcap);
        for (char *s = line; *s;) {
            while (*s == ' ' || *s == '\t' || *s == '\r') s++;
            if (!*s) break;
            if (*s < '0' || *s > '9') { fprintf(stderr, "bad character in row %d\n", n); return 2; }
            long v = 0;
            while (*s >= '0' && *s <= '9') { v = v * 10 + (*s - '0'); s++; if (v > 1 << 20) break; }
            if (cert) {  /* ca-tools certificate: the vector (1, x, y) in base q, most significant digit first */
                if (v / P != 1 || v >= 2L * P) { fprintf(stderr, "certificate entry %ld is not (1, x, y)\n", v); return 2; }
                v -= P;
            }
            if (v >= P) { fprintf(stderr, "point id %ld out of range\n", v); return 2; }
            if (kc == kcap) { kcap *= 2; row = realloc(row, sizeof(uint16_t) * kcap); }
            row[kc++] = (uint16_t)v;
        }
        if (k >= 0 && kc != k) { fprintf(stderr, "rows differ in length (%ld vs %d)\n", kc, k); return 2; }
        k = (int)kc; Hp[n++] = row;
        if (ch == EOF) break;
    }
    fclose(f);
    if (n < 1 || k < 3) { fprintf(stderr, "no array\n"); return 2; }
    for (int r = 0; r < n; r++) {
        X[r] = malloc(k); Y[r] = malloc(k);
        for (int c = 0; c < k; c++) { X[r][c] = (uint8_t)(Hp[r][c] / q); Y[r][c] = (uint8_t)(Hp[r][c] % q); }
    }
    long from = 2, to = k;
    if (argc > 5) { from = atol(argv[4]); to = atol(argv[5]); }
    if (from < 2) from = 2;
    if (to > k) to = k;
    int *ident = malloc(sizeof(int) * k);
    for (int i = 0; i < k; i++) ident[i] = i;
    long long triples = 0;
    clock_t t0 = clock(), tl = t0;
    for (long c = from; c < to; c++) {
        cc = (int)c;
        for (int r = 0; r < n; r++) base[r] = LBL + (size_t)Hp[r][c] * P;
        group(0, ident, (int)c);
        clear_reports();
        triples += (long long)c * (c - 1) / 2;
        if ((double)(clock() - tl) / CLOCKS_PER_SEC > 60) {
            tl = clock();
            fprintf(stderr, "c %ld of [%ld, %ld): %.0f s, %lld uncovered so far\n", c, from, to, (double)(tl - t0) / CLOCKS_PER_SEC, bad);
        }
    }
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("SCPHF(%d; %d, %d^2, 3): %lld column triples checked (largest column in [%ld, %ld)), %lld never non-collinear",
           n, k, q, triples, from, to, bad);
    if (bad) printf(" (first: columns %d, %d, %d)", fa, fb, fc);
    printf("; %.0f s, %lld label tests beyond the splits", secs, work);
    if (falsealarm) printf("; %lld reported pairs rejected by the determinant (method error)", falsealarm);
    printf("\n");
    /* covering-array spot check */
    long N = (long)n * (q * q * q - q) + q, missing = 0;
    int Q3 = q * q * q;
    uint32_t *stamp = calloc((size_t)Q3, sizeof(uint32_t));
    uint64_t s = 0x2545F4914F6CDD1DULL ^ (uint64_t)k * 0x9E3779B97F4A7C15ULL;
    for (long t = 1; t <= samples; t++) {
        int col[3];
        do {
            for (int i = 0; i < 3; i++) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; col[i] = (int)(s % (uint64_t)k); }
        } while (col[0] == col[1] || col[0] == col[2] || col[1] == col[2]);
        int seen = 0;
        for (int r = 0; r < n; r++)
            for (int u1 = 0; u1 < q; u1++)
                for (int u2 = 0; u2 < q; u2++) {
                    if (u1 == 0 && u2 == 0 && r > 0) continue;
                    int bse[3];
                    for (int i = 0; i < 3; i++) bse[i] = ADD[MUL[u1][X[r][col[i]]]][MUL[u2][Y[r][col[i]]]];
                    for (int u0 = 0; u0 < q; u0++) {
                        int code = (ADD[u0][bse[0]] * q + ADD[u0][bse[1]]) * q + ADD[u0][bse[2]];
                        if (stamp[code] != (uint32_t)t) { stamp[code] = (uint32_t)t; seen++; }
                    }
                }
        if (seen != Q3) missing++;
    }
    printf("CA(%ld; 3, %d, %d): %ld random column triples, %ld missing a tuple\n", N, k, q, samples, missing);
    int fail = bad || missing || falsealarm;
    printf("%s\n", fail ? "FAIL" : "PASS");
    return fail ? 1 : 0;
}
