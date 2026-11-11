/* t4ref: strength-4 Sherwood CPHFs whose rows are mostly affine progressions, and their exact check.
   A row is a progression when u_{c+1} = A u_c for every column c, A an invertible 4x4 matrix over GF(q) (solved
   from the data and verified on every column). In such a row det(u_{c1+s}, .., u_{c4+s}) = det(A)^s det(u_{c1}, ..,
   u_{c4}), so a set of four columns fails in every progression row exactly when its shift to column 0 does. The
   representatives {0 < x < y < z} failing in every progression row are found for each x by refinement: with h1, h2
   spanning the annihilator of span(u_0, u_x) in a row, column c gets the class [h1.u_c : h2.u_c] of PG(1,q), or WILD
   when both are 0, and {0, x, y, z} fails in the row exactly when y or z is WILD or their classes are equal (a row in
   which u_x is a multiple of u_0 fails for every y, z and is skipped for this x). A subproblem (A, B) stands for the
   pairs inside A and the pairs between A and B; classing it by one row splits the pairs failing that row exactly
   into (A_z, A_w + B_z + B_w) for each class z and (A_w, B), with no pair twice; the rest are ruled out. Every
   representative is rechecked by rank in every progression row, and every shift of it is tested in the other rows.
   Completeness: failing + ruled out = C(k-1-x, 2) for every x, summed C(k-1, 3).
   Modes:
     t4ref check FAMILY q [threads]
     t4ref build q K nA nB nO seed OUT [threads]   (nA rows a^j in GF(q^3), nB rows (b^j, j) in GF(q^2) x GF(q),
                                                   nO random rows, the last one repaired to cover what is left) */
#include "gfq.h"
#include "famio.h"
#include <pthread.h>
#include <string.h>
#define WILD 255
typedef struct { uint8_t m[4][4]; } mat4;
static int q, NT = 3;
static long K;
static int nrows, nP, nO; static int Prow[64], Orow[64];
static uint8_t *U;                 /* U[(r*K + c)*4 + j] */
#define UU(r, c) (U + (((size_t)(r) * K + (c)) * 4))
static uint8_t dot4(const uint8_t *a, const uint8_t *b) {
    return GADD[GADD[GMUL[a[0]][b[0]]][GMUL[a[1]][b[1]]]][GADD[GMUL[a[2]][b[2]]][GMUL[a[3]][b[3]]]];
}
static int mat4_inv(const mat4 *M, mat4 *R) {
    uint8_t a[4][8];
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { a[i][j] = M->m[i][j]; a[i][4 + j] = (i == j); }
    for (int col = 0; col < 4; col++) {
        int piv = -1; for (int i = col; i < 4; i++) if (a[i][col]) { piv = i; break; }
        if (piv < 0) return 0;
        if (piv != col) for (int j = 0; j < 8; j++) { uint8_t t = a[col][j]; a[col][j] = a[piv][j]; a[piv][j] = t; }
        uint8_t iv = GINV[a[col][col]];
        for (int j = 0; j < 8; j++) a[col][j] = GMUL[a[col][j]][iv];
        for (int i = 0; i < 4; i++) if (i != col && a[i][col]) { uint8_t f = a[i][col]; for (int j = 0; j < 8; j++) a[i][j] = GSUB[a[i][j]][GMUL[f][a[col][j]]]; }
    }
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) R->m[i][j] = a[i][4 + j];
    return 1;
}
static void mat4_vec(const mat4 *M, const uint8_t *v, uint8_t *out) {
    for (int i = 0; i < 4; i++) out[i] = dot4(M->m[i], v);
}
/* classify row r: 1 progression (A returned), 0 other, -1 dead (does not span) */
static int classify(int r, mat4 *A) {
    uint8_t basis[4][4]; int sel[4], nb = 0;
    for (long c = 0; c + 1 < K && nb < 4; c++) {
        memcpy(basis[nb], UU(r, c), 4);
        if (gf_rank4((const uint8_t (*)[4])basis, nb + 1) == nb + 1) sel[nb++] = (int)c;
    }
    if (nb < 4) { /* does the row span at all (including the last column)? */
        uint8_t all[4][4]; int m = 0;
        for (long c = 0; c < K && m < 4; c++) { memcpy(all[m], UU(r, c), 4); if (gf_rank4((const uint8_t (*)[4])all, m + 1) == m + 1) m++; }
        return m < 4 ? -1 : 0;
    }
    mat4 Ucol, Unext, Ui;  /* columns u_sel and u_sel+1: A Ucol = Unext */
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { Ucol.m[j][i] = UU(r, sel[i])[j]; Unext.m[j][i] = UU(r, sel[i] + 1)[j]; }
    if (!mat4_inv(&Ucol, &Ui)) return 0;
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) {
        uint8_t s = 0; for (int l = 0; l < 4; l++) s = GADD[s][GMUL[Unext.m[i][l]][Ui.m[l][j]]];
        A->m[i][j] = s;
    }
    mat4 Ainv; if (!mat4_inv(A, &Ainv)) return 0;
    for (long c = 0; c + 1 < K; c++) { uint8_t w[4]; mat4_vec(A, UU(r, c), w); if (memcmp(w, UU(r, c + 1), 4)) return 0; }
    return 1;
}
/* annihilator of span(a, b) (rank 2): h1, h2 */
static void annih2(const uint8_t *a, const uint8_t *b, uint8_t h1[4], uint8_t h2[4]) {
    uint8_t m[2][4]; memcpy(m[0], a, 4); memcpy(m[1], b, 4);
    int pc[2], r = 0;
    for (int col = 0; col < 4 && r < 2; col++) {
        int piv = -1; for (int i = r; i < 2; i++) if (m[i][col]) { piv = i; break; }
        if (piv < 0) continue;
        if (piv != r) for (int j = 0; j < 4; j++) { uint8_t t = m[r][j]; m[r][j] = m[piv][j]; m[piv][j] = t; }
        uint8_t iv = GINV[m[r][col]]; for (int j = 0; j < 4; j++) m[r][j] = GMUL[m[r][j]][iv];
        for (int i = 0; i < 2; i++) if (i != r && m[i][col]) { uint8_t f = m[i][col]; for (int j = 0; j < 4; j++) m[i][j] = GSUB[m[i][j]][GMUL[f][m[r][j]]]; }
        pc[r++] = col;
    }
    int fc[2], nf = 0; for (int col = 0; col < 4; col++) if (col != pc[0] && col != pc[1]) fc[nf++] = col;
    uint8_t *hs[2] = {h1, h2};
    for (int t = 0; t < 2; t++) {
        memset(hs[t], 0, 4); hs[t][fc[t]] = 1;
        for (int i = 0; i < 2; i++) hs[t][pc[i]] = GNEG[m[i][fc[t]]];
    }
}
/* ---- enumeration ---- */
typedef struct { int x, y, z; } rep_t;
typedef struct {
    int tid; int R; int rowsx[64]; uint8_t H1[64][4], H2[64][4];
    int **sa, **sb, **sub; uint8_t *ca, *cb;
    unsigned long long failing, ruled, wildrows, xdone;
    rep_t *reps; size_t nreps, capreps; int overflow; long x;
} work_t;
static size_t REPCAP = 20000000;
static uint8_t cls(work_t *W, int d, int c) {
    int r = W->rowsx[d];
    const uint8_t *u = UU(r, c);
    uint8_t a = dot4(W->H1[d], u), b = dot4(W->H2[d], u);
    if (a) return GMUL[b][GINV[a]];
    if (b) return (uint8_t)q;
    return WILD;
}
static void report(work_t *W, int y, int z) {
    if (y > z) { int t = y; y = z; z = t; }
    W->failing++;
    if (W->nreps == W->capreps) {
        if (W->capreps * 2 > REPCAP) { W->overflow = 1; return; }
        W->capreps = W->capreps ? W->capreps * 2 : 1024; W->reps = realloc(W->reps, W->capreps * sizeof(rep_t));
    }
    W->reps[W->nreps].x = (int)W->x; W->reps[W->nreps].y = y; W->reps[W->nreps].z = z; W->nreps++;
}
static void solve(work_t *W, int d, int *A, int na, int *B, int nb) {
    unsigned long long pairs = (unsigned long long)na * (na - 1) / 2 + (unsigned long long)na * nb;
    if (!pairs) return;
    if (d == W->R) {
        for (int i = 0; i < na; i++) { for (int j = i + 1; j < na; j++) report(W, A[i], A[j]); for (int j = 0; j < nb; j++) report(W, A[i], B[j]); }
        return;
    }
    if (pairs <= 12) {
        for (int i = 0; i < na; i++) for (int j = i + 1; j < na + nb; j++) {
            int y = A[i], z = j < na ? A[j] : B[j - na], fail = 1;
            for (int e = d; e < W->R && fail; e++) { uint8_t c1 = cls(W, e, y), c2 = cls(W, e, z); if (c1 != WILD && c2 != WILD && c1 != c2) fail = 0; }
            if (fail) report(W, y, z); else W->ruled++;
        }
        return;
    }
    int NC = q + 2;  /* classes 0..q, WILD as q+1 */
    int cntA[34] = {0}, cntB[34] = {0}, offA[35], offB[35];
    uint8_t *ca = W->ca, *cb = W->cb;  /* scratch for this depth: classes; reused safely because filled before recursion */
    /* classes must survive recursion: store them in the sorted arrays' companion order instead */
    int *sa = W->sa[d], *sb = W->sb[d], *sub = W->sub[d];
    for (int i = 0; i < na; i++) { uint8_t c = cls(W, d, A[i]); ca[i] = c == WILD ? (uint8_t)(q + 1) : c; cntA[ca[i]]++; }
    for (int i = 0; i < nb; i++) { uint8_t c = cls(W, d, B[i]); cb[i] = c == WILD ? (uint8_t)(q + 1) : c; cntB[cb[i]]++; }
    offA[0] = offB[0] = 0;
    for (int z = 0; z < NC; z++) { offA[z + 1] = offA[z] + cntA[z]; offB[z + 1] = offB[z] + cntB[z]; }
    { int pa[35], pb[35]; memcpy(pa, offA, sizeof pa); memcpy(pb, offB, sizeof pb);
      for (int i = 0; i < na; i++) sa[pa[ca[i]]++] = A[i];
      for (int i = 0; i < nb; i++) sb[pb[cb[i]]++] = B[i]; }
    int wa = offA[q + 1], nwa = cntA[q + 1], wb = offB[q + 1], nwb = cntB[q + 1];
    unsigned long long subpairs = 0;
    for (int z = 0; z <= q; z++) {
        int nA = cntA[z]; if (!nA) continue;
        int m = 0;
        for (int i = 0; i < nwa; i++) sub[m++] = sa[wa + i];
        for (int i = 0; i < cntB[z]; i++) sub[m++] = sb[offB[z] + i];
        for (int i = 0; i < nwb; i++) sub[m++] = sb[wb + i];
        subpairs += (unsigned long long)nA * (nA - 1) / 2 + (unsigned long long)nA * m;
        solve(W, d + 1, sa + offA[z], nA, sub, m);
    }
    if (nwa) {
        subpairs += (unsigned long long)nwa * (nwa - 1) / 2 + (unsigned long long)nwa * nb;
        /* B for (A_w, B) is all of B: take it from sb (any order) */
        solve(W, d + 1, sa + wa, nwa, sb, nb);
    }
    W->ruled += pairs - subpairs;
}
static void *enum_thread(void *arg) {
    work_t *W = arg;
    int *all = malloc(sizeof(int) * K);
    for (long x = 1 + W->tid; x <= K - 3; x += NT) {
        W->x = x; W->R = 0;
        for (int i = 0; i < nP; i++) {
            int r = Prow[i]; uint8_t v[2][4]; memcpy(v[0], UU(r, 0), 4); memcpy(v[1], UU(r, x), 4);
            if (gf_rank4((const uint8_t (*)[4])v, 2) < 2) { W->wildrows++; continue; }
            W->rowsx[W->R] = r; annih2(UU(r, 0), UU(r, x), W->H1[W->R], W->H2[W->R]); W->R++;
        }
        int na = 0; for (long c = x + 1; c < K; c++) all[na++] = (int)c;
        unsigned long long f0 = W->failing, r0 = W->ruled;
        solve(W, 0, all, na, NULL, 0);
        unsigned long long tot = (unsigned long long)na * (na - 1) / 2;
        if (W->failing - f0 + W->ruled - r0 != tot) { fprintf(stderr, "INTERNAL CHECK FAILED: x=%ld counts %llu + %llu != %llu\n", x, W->failing - f0, W->ruled - r0, tot); exit(4); }
        W->xdone++;
        if (W->overflow) break;
    }
    free(all);
    return NULL;
}
static rep_t *REPS; static size_t NREPS;
static int enumerate(unsigned long long *failing, unsigned long long *ruled) {
    pthread_t th[64]; work_t *Ws = calloc(NT, sizeof(work_t));
    for (int t = 0; t < NT; t++) {
        work_t *W = &Ws[t]; W->tid = t;
        W->sa = malloc(sizeof(int *) * 66); W->sb = malloc(sizeof(int *) * 66); W->sub = malloc(sizeof(int *) * 66);
        for (int d = 0; d < 66; d++) { W->sa[d] = malloc(sizeof(int) * K); W->sb[d] = malloc(sizeof(int) * K); W->sub[d] = malloc(sizeof(int) * K); }
        W->ca = malloc(K); W->cb = malloc(K);
        pthread_create(&th[t], NULL, enum_thread, W);
    }
    *failing = *ruled = 0; NREPS = 0; size_t cap = 0; int over = 0; unsigned long long wr = 0, xd = 0;
    for (int t = 0; t < NT; t++) {
        pthread_join(th[t], NULL); work_t *W = &Ws[t];
        *failing += W->failing; *ruled += W->ruled; wr += W->wildrows; xd += W->xdone; over |= W->overflow;
        if (NREPS + W->nreps > cap) { cap = NREPS + W->nreps; REPS = realloc(REPS, cap * sizeof(rep_t) + 1); }
        memcpy(REPS + NREPS, W->reps, W->nreps * sizeof(rep_t)); NREPS += W->nreps; free(W->reps);
        for (int d = 0; d < 66; d++) { free(W->sa[d]); free(W->sb[d]); free(W->sub[d]); }
        free(W->sa); free(W->sb); free(W->sub); free(W->ca); free(W->cb);
    }
    free(Ws);
    printf("enumeration: x = 1..%ld (%llu done), (x, row) wildcards %llu, pairs failing every progression row %llu + ruled out %llu = %llu (C(k-1,3) = %llu)%s\n",
           K - 3, xd, wr, *failing, *ruled, *failing + *ruled,
           (unsigned long long)(K - 1) * (K - 2) * (K - 3) / 6, over ? " OVERFLOW (too many representatives)" : "");
    return !over;
}
/* recheck by rank and shift tests in the other rows; returns number of uncovered sets */
static unsigned long long shift_tests(unsigned long long *tested, int verbose) {
    unsigned long long bad = 0; *tested = 0; int shown = 0;
    for (size_t i = 0; i < NREPS; i++) {
        rep_t *R = &REPS[i];
        for (int pi = 0; pi < nP; pi++) {
            int r = Prow[pi]; uint8_t v[4][4];
            memcpy(v[0], UU(r, 0), 4); memcpy(v[1], UU(r, R->x), 4); memcpy(v[2], UU(r, R->y), 4); memcpy(v[3], UU(r, R->z), 4);
            if (gf_rank4((const uint8_t (*)[4])v, 4) == 4) { fprintf(stderr, "INTERNAL CHECK FAILED: representative 0 %d %d %d covered by progression row %d\n", R->x, R->y, R->z, r); exit(4); }
        }
        for (long a = 0; a + R->z < K; a++) {
            int cov = 0;
            for (int oi = 0; oi < nO && !cov; oi++) {
                int r = Orow[oi]; uint8_t v[4][4];
                memcpy(v[0], UU(r, a), 4); memcpy(v[1], UU(r, a + R->x), 4); memcpy(v[2], UU(r, a + R->y), 4); memcpy(v[3], UU(r, a + R->z), 4);
                if (gf_rank4((const uint8_t (*)[4])v, 4) == 4) cov = 1;
            }
            (*tested)++;
            if (!cov) { bad++; if (verbose && (shown < 20 || getenv("T4_LIST"))) { printf("U %ld %ld %ld %ld\n", a, a + R->x, a + R->y, a + R->z); shown++; } }
        }
    }
    return bad;
}
/* ---- check mode ---- */
static int do_check(const char *path) {
    fam_t F; if (!fam_read(path, q, &F)) return 2;
    K = F.k; nrows = F.n; U = F.u;
    if (K < 5) { fprintf(stderr, "k too small\n"); return 2; }
    nP = nO = 0; int dead = 0;
    for (int r = 0; r < nrows; r++) {
        mat4 A; int c = classify(r, &A);
        if (c == 1) Prow[nP++] = r; else if (c == 0) Orow[nO++] = r; else dead++;
        printf("row %d: %s\n", r, c == 1 ? "progression" : c == 0 ? "other" : "dead (does not span GF(q)^4)");
    }
    printf("family %s: n = %d rows, k = %ld, q = %d: %d progression, %d other, %d dead\n", path, nrows, K, q, nP, nO, dead);
    if (!nP) { printf("no progression rows: use another method\nRESULT FAIL\n"); return 3; }
    unsigned long long fl, ru; if (!enumerate(&fl, &ru)) { printf("RESULT FAIL\n"); return 3; }
    unsigned long long tested, bad = shift_tests(&tested, 1);
    printf("representatives (sets {0,x,y,z} failing every progression row) %zu, rechecked by rank; shifts tested in the %d other rows %llu, uncovered %llu\n", NREPS, nO, tested, bad);
    printf("%s\n", bad ? "RESULT FAIL" : "RESULT PASS");
    if (!bad) printf("SCPHF-type CPHF(%d; %ld, %d, 4): every set of four columns covered\n", nrows, K, q);
    return bad ? 1 : 0;
}
/* ---- build mode ---- */
static uint64_t rng;
static uint64_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static long period_of(const mat4 *M, long cap) { /* period of u0 = (1,1,0,0) under M */
    uint8_t s[4] = {1, 1, 0, 0}, v[4], w[4]; memcpy(v, s, 4);
    for (long j = 1; j <= cap; j++) { mat4_vec(M, v, w); memcpy(v, w, 4); if (!memcmp(v, s, 4)) return j; }
    return -1;
}
static int NS_ROWS = 0;
static int do_build(long Kb, int nA, int nB, int nOr, uint64_t seed, const char *out) {
    int nS = NS_ROWS; K = Kb; nrows = nS + nA + nB + nOr; rng = seed * 0x9E3779B97F4A7C15ULL + 12345;
    U = calloc((size_t)nrows * K * 4, 1);
    char desc[8192]; int dl = 0; dl += snprintf(desc + dl, sizeof desc - dl, "#");
    nP = 0; nO = 0;
    for (int r = 0; r < nS + nA + nB; r++) {
        mat4 M; memset(&M, 0, sizeof M); M.m[0][0] = 1;
        uint8_t f[4]; long per = 0;
        if (r < nS) {  /* Singer row: multiplication by a primitive alpha of GF(q^4) on (c0..c3), not affine */
            for (;;) {
                for (int i = 0; i < 4; i++) f[i] = (uint8_t)(rnd() % q); if (!f[0]) continue;
                mat4 T; memset(&T, 0, sizeof T);
                T.m[0][3] = GNEG[f[0]]; T.m[1][0] = 1; T.m[1][3] = GNEG[f[1]]; T.m[2][1] = 1; T.m[2][3] = GNEG[f[2]]; T.m[3][2] = 1; T.m[3][3] = GNEG[f[3]];
                uint8_t s0[4] = {1, 0, 0, 0}, vv[4], ww[4]; memcpy(vv, s0, 4); long j; long qq4 = (long)q * q * q * q - 1;
                for (j = 1; j <= qq4; j++) { mat4_vec(&T, vv, ww); memcpy(vv, ww, 4); if (!memcmp(vv, s0, 4)) break; }
                if (j != qq4) continue;
                M = T; per = j; break;
            }
            dl += snprintf(desc + dl, sizeof desc - dl, " S(X^4+%dX^3+%dX^2+%dX+%d, period %ld)", f[3], f[2], f[1], f[0], per);
            uint8_t v0[4] = {1, 0, 0, 0}, w0[4];
            for (long c = 0; c < K; c++) { memcpy(UU(r, c), v0, 4); mat4_vec(&M, v0, w0); memcpy(v0, w0, 4); }
            Prow[nP++] = r; continue;
        }
        if (r < nS + nA) {  /* x -> alpha x on GF(q)[X]/(X^3 + f2 X^2 + f1 X + f0), basis 1, X, X^2; irreducible = no root */
            for (;;) {
                f[0] = (uint8_t)(1 + rnd() % (q - 1)); f[1] = (uint8_t)(rnd() % q); f[2] = (uint8_t)(rnd() % q);
                int root = 0; for (int x = 0; x < q && !root; x++) { uint8_t x2 = GMUL[x][x], x3 = GMUL[x2][x];
                    if (GADD[GADD[x3][GMUL[f[2]][x2]]][GADD[GMUL[f[1]][x]][f[0]]] == 0) root = 1; }
                if (root) continue;
                mat4 T; memset(&T, 0, sizeof T); T.m[0][0] = 1;
                /* (c0, c1, c2) -> (-f0 c2, c0 - f1 c2, c1 - f2 c2) on coordinates 1..3 */
                T.m[1][3] = GNEG[f[0]]; T.m[2][1] = 1; T.m[2][3] = GNEG[f[1]]; T.m[3][2] = 1; T.m[3][3] = GNEG[f[2]];
                per = period_of(&T, (long)q * q * q);
                if (per != (long)q * q * q - 1) continue;   /* alpha primitive in GF(q^3): period q^3 - 1 */
                M = T; break;
            }
            dl += snprintf(desc + dl, sizeof desc - dl, " A(X^3+%dX^2+%dX+%d, period %ld)", f[2], f[1], f[0], per);
        } else {      /* (y, z) -> (beta y, z + 1): GF(q)[X]/(X^2 + g1 X + g0) on coordinates 1, 2, translation on 3 */
            for (;;) {
                f[0] = (uint8_t)(1 + rnd() % (q - 1)); f[1] = (uint8_t)(rnd() % q);
                int root = 0; for (int x = 0; x < q && !root; x++) if (GADD[GADD[GMUL[x][x]][GMUL[f[1]][x]]][f[0]] == 0) root = 1;
                if (root) continue;
                mat4 T; memset(&T, 0, sizeof T); T.m[0][0] = 1;
                T.m[1][2] = GNEG[f[0]]; T.m[2][1] = 1; T.m[2][2] = GNEG[f[1]];
                T.m[3][3] = 1; T.m[3][0] = 1;     /* z -> z + 1 (times the leading 1) */
                per = period_of(&T, (long)q * q * q * 4);
                if (per != (long)GP * ((long)q * q - 1)) continue;   /* beta primitive in GF(q^2): period p(q^2 - 1) */
                M = T; break;
            }
            dl += snprintf(desc + dl, sizeof desc - dl, " B(X^2+%dX+%d, period %ld)", f[1], f[0], per);
        }
        uint8_t v[4] = {1, 1, 0, 0}, w[4];
        for (long c = 0; c < K; c++) { memcpy(UU(r, c), v, 4); mat4_vec(&M, v, w); memcpy(v, w, 4); }
        Prow[nP++] = r;
    }
    printf("cyclic rows:%s\n", desc + 1); fflush(stdout);
    unsigned long long fl, ru;
    if (!enumerate(&fl, &ru)) { printf("too many representatives; add cyclic rows\n"); return 3; }
    printf("representatives failing every cyclic row: %zu\n", NREPS); fflush(stdout);
    /* random rows: all but the last drawn at random; the shifted sets still uncovered are kept */
    typedef struct { int c[4]; } set4; set4 *left = NULL; size_t nleft = 0, capl = 0;
    int firstO = nS + nA + nB;
    for (int oi = 0; oi < nOr; oi++) {
        int r = firstO + oi;
        for (long c = 0; c < K; c++) { uint8_t *u = UU(r, c); u[0] = 1; u[1] = (uint8_t)(rnd() % q); u[2] = (uint8_t)(rnd() % q); u[3] = (uint8_t)(rnd() % q); }
    }
    /* the sets left after the first nOr-1 random rows (never more than LEFTCAP kept) */
    if (nOr == 0) { printf("no random rows: %zu representatives, each shift would need covering\n", NREPS); return NREPS ? 3 : 0; }
    for (size_t i = 0; i < NREPS; i++) {
        rep_t *R = &REPS[i];
        for (long a = 0; a + R->z < K; a++) {
            int cov = 0;
            for (int oi = 0; oi + 1 < nOr && !cov; oi++) {
                int r = firstO + oi; uint8_t v[4][4];
                memcpy(v[0], UU(r, a), 4); memcpy(v[1], UU(r, a + R->x), 4); memcpy(v[2], UU(r, a + R->y), 4); memcpy(v[3], UU(r, a + R->z), 4);
                if (gf_rank4((const uint8_t (*)[4])v, 4) == 4) cov = 1;
            }
            if (!cov) {
                if (nleft >= 4000000) { printf("more than 4,000,000 shifted sets left for the last row; add rows\n"); return 3; }
                if (nleft == capl) { capl = capl ? capl * 2 : 1024; left = realloc(left, capl * sizeof(set4)); }
                left[nleft].c[0] = (int)a; left[nleft].c[1] = (int)(a + R->x); left[nleft].c[2] = (int)(a + R->y); left[nleft].c[3] = (int)(a + R->z); nleft++;
            }
        }
    }
    printf("shifted sets left for the last row: %zu\n", nleft); fflush(stdout);
    if (nOr == 0 && nleft) { printf("no random rows to cover them\n"); return 3; }
    if (nleft > 4000000) { printf("too many sets left (%zu); add rows\n", nleft); return 3; }
    /* index: the left sets through each column */
    long *deg = calloc(K + 1, sizeof(long)); for (size_t i = 0; i < nleft; i++) for (int j = 0; j < 4; j++) deg[left[i].c[j] + 1]++;
    for (long c = 0; c < K; c++) deg[c + 1] += deg[c];
    size_t *inc = malloc(sizeof(size_t) * (nleft * 4 + 1)); long *fillp = calloc(K, sizeof(long));
    for (size_t i = 0; i < nleft; i++) for (int j = 0; j < 4; j++) { int c = left[i].c[j]; inc[deg[c] + fillp[c]++] = i; }
    if (nOr > 0) {
        int r = firstO + nOr - 1; long it = 0;
        size_t *unc = malloc(sizeof(size_t) * (nleft + 1)); size_t nunc = 0;
        for (size_t i = 0; i < nleft; i++) { uint8_t v[4][4]; for (int j = 0; j < 4; j++) memcpy(v[j], UU(r, left[i].c[j]), 4);
            if (gf_rank4((const uint8_t (*)[4])v, 4) < 4) unc[nunc++] = i; }
        printf("last row: %zu of the %zu left sets uncovered at first\n", nunc, nleft);
        for (;; it++) {
            /* drop the sets now covered from the front of the list */
            while (nunc) { size_t i = unc[nunc - 1]; uint8_t v[4][4]; for (int j = 0; j < 4; j++) memcpy(v[j], UU(r, left[i].c[j]), 4);
                if (gf_rank4((const uint8_t (*)[4])v, 4) == 4) nunc--; else break; }
            size_t bad = nunc, badi = nunc ? unc[nunc - 1] : 0;
            if (!bad) {  /* confirm over all left sets */
                for (size_t i = 0; i < nleft; i++) { uint8_t v[4][4]; for (int j = 0; j < 4; j++) memcpy(v[j], UU(r, left[i].c[j]), 4);
                    if (gf_rank4((const uint8_t (*)[4])v, 4) < 4) unc[nunc++] = i; }
                if (!nunc) break; else continue;
            }
            if (it > 2000000) { printf("last row repair failed (%zu left)\n", bad); return 3; }
            /* repair: move one column of an uncovered set to the sampled point leaving the fewest left sets through
               that column uncovered in this row (never more than now) */
            int c = left[badi].c[rnd() % 4];
            uint8_t *u = UU(r, c), keep[4]; memcpy(keep, u, 4);
            int bestcnt = 1 << 30; uint8_t bestp[4]; memcpy(bestp, u, 4);
            for (int tries = 0; tries < 96; tries++) {
                if (tries) { u[1] = (uint8_t)(rnd() % q); u[2] = (uint8_t)(rnd() % q); u[3] = (uint8_t)(rnd() % q); }
                int cntu = 0;
                for (long ii = deg[c]; ii < deg[c + 1] && cntu < bestcnt; ii++) {
                    size_t i = inc[ii];
                    uint8_t v[4][4]; for (int j = 0; j < 4; j++) memcpy(v[j], UU(r, left[i].c[j]), 4);
                    if (gf_rank4((const uint8_t (*)[4])v, 4) < 4) cntu++;
                }
                if (cntu < bestcnt) { bestcnt = cntu; memcpy(bestp, u, 4); if (!cntu) break; }
            }
            memcpy(u, bestp, 4);
            /* the sets through c that are now uncovered go back on the list */
            for (long ii = deg[c]; ii < deg[c + 1]; ii++) { size_t i = inc[ii];
                uint8_t v[4][4]; for (int j = 0; j < 4; j++) memcpy(v[j], UU(r, left[i].c[j]), 4);
                if (gf_rank4((const uint8_t (*)[4])v, 4) < 4) { int dup = 0; for (size_t z = nunc; z-- > 0 && z + 64 > nunc;) if (unc[z] == i) { dup = 1; break; }
                    if (!dup) { if (nunc == nleft) break; unc[nunc++] = i; } } }
        }
        printf("last row repaired in %ld rounds\n", it);
    }
    FILE *f = fopen(out, "w"); if (!f) { perror(out); return 2; }
    long N = nS ? (long)nrows * ((long)q * q * q * q - 1) + 1 : (long)nrows * ((long)q * q * q * q - q) + q;
    fprintf(f, "# CA_%ld_4_%ld_%d: CPHF(%d; %ld, %d, 4)%s, CA(%ld; 4, %ld, %d); Conway coding of GF(%d)\n", N, K, q, nrows, K, q, nS ? ", vectors of GF(q)^4 (not all affine)" : ", affine points (first coordinate 1)", N, K, q, q);
    fprintf(f, "# t4ref build %d %ld %d %d %d %llu %d (nS): rows 0..%d progressions u_{c+1} = M u_c (S: multiplication by a primitive element of GF(q^4) from (1,0,0,0), not affine; A: a^j in GF(q^3) from the point 1; B: (b^j, j) in GF(q^2) x GF(q) from (1,0,0)):%s; rows %d..%d random affine points\n",
            q, K, nA, nB, nOr, (unsigned long long)seed, nS, nS + nA + nB - 1, desc + 1, nS + nA + nB, nrows - 1);
    for (int r = 0; r < nrows; r++) {
        for (long c = 0; c < K; c++) { const uint8_t *u = UU(r, c); fprintf(f, c ? " %d" : "%d", ((u[0] * q + u[1]) * q + u[2]) * q + u[3]); }
        fputc('\n', f);
    }
    fclose(f);
    printf("wrote %s: n = %d, k = %ld, N = %ld\n", out, nrows, K, N);
    return 0;
}
int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IOLBF, 0);
    if (argc >= 4 && !strcmp(argv[1], "check")) {
        q = atoi(argv[3]); if (!gf_init(q)) { fprintf(stderr, "bad q\n"); return 2; }
        if (argc > 4) NT = atoi(argv[4]);
        return do_check(argv[2]);
    }
    if (argc >= 9 && !strcmp(argv[1], "build")) {
        q = atoi(argv[2]); if (!gf_init(q)) { fprintf(stderr, "bad q\n"); return 2; }
        if (argc > 9) NT = atoi(argv[9]);
        if (argc > 10) NS_ROWS = atoi(argv[10]);
        return do_build(atol(argv[3]), atoi(argv[4]), atoi(argv[5]), atoi(argv[6]), strtoull(argv[7], 0, 10), argv[8]);
    }
    fprintf(stderr, "usage: t4ref check FAMILY q [threads] | t4ref build q K nA nB nO seed OUT [threads]\n");
    return 2;
}
