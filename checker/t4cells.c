/* t4cells: second exact check of a strength-4 CPHF (ca-tools format), written separately from t4ref.c.
   Rows that are progressions (u_{c+1} = A u_c, A invertible; solved from the last columns, verified on all) reduce the
   check to the sets {0, x, y, z}. In a progression row r map every column c > 0 to the image of u_c in V/<u_0> (V =
   GF(q)^4), a point of PG(2,q), or Z when u_c is a multiple of u_0. {0, x, y, z} fails in row r exactly when the three
   images are dependent: one is Z, two coincide, or the three are collinear; equivalently all three lie on a common
   line l of PG(2,q), with Z on every line ("cells"). The columns are bucketed by every line through their image, row
   after row (depth first) until a bucket is small; the triples of a bucket are then listed, kept only when every
   bucketed row's line is the triple's canonical line in that row (so each triple is reported once), and tested by
   rank in the remaining progression rows. Every reported triple is rechecked by rank in every progression row and
   each of its shifts is tested in the other rows. Usage: t4cells FAMILY q [threads]; T4_LIST lists uncovered sets. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
static int Q, P_, E_;
static uint8_t FA[32][32], FM[32][32], FN[32], FI[32];
static int field(int q) {
    Q = q; P_ = 0; for (int d = 2; d <= q; d++) if (q % d == 0) { P_ = d; break; }
    E_ = 0; for (int x = 1; x < q; x *= P_) E_++;
    int conway[6] = {0};  /* x^E = -(c0 + c1 x + ...) */
    if (q == 4 || q == 8 || q == 16) { conway[0] = 1; conway[1] = 1; }
    else if (q == 9) { conway[0] = 2; conway[1] = 2; }
    else if (q == 25) { conway[0] = 2; conway[1] = 4; }
    else if (E_ != 1) return 0;
    /* times_x on digit vectors, then multiplication by shift and add */
    int tx[32];
    for (int a = 0; a < q; a++) {
        int d[6] = {0}, u = a; for (int i = 0; i < E_; i++) { d[i] = u % P_; u /= P_; }
        int top = E_ > 1 ? d[E_ - 1] : 0, nd[6] = {0};
        if (E_ == 1) { tx[a] = a; continue; }
        for (int i = E_ - 1; i > 0; i--) nd[i] = d[i - 1];
        for (int i = 0; i < E_; i++) nd[i] = ((nd[i] - top * conway[i]) % P_ + P_) % P_;
        int s = 0, pw = 1; for (int i = 0; i < E_; i++) { s += nd[i] * pw; pw *= P_; } tx[a] = s;
    }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int s = 0, pw = 1, x = a, y = b; for (int i = 0; i < E_; i++) { s += ((x % P_ + y % P_) % P_) * pw; pw *= P_; x /= P_; y /= P_; }
        FA[a][b] = (uint8_t)s;
    }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        if (E_ == 1) { FM[a][b] = (uint8_t)(a * b % q); continue; }
        /* a * b = sum over digits of b: b_i (a x^i) */
        int acc = 0, ax = a, y = b;
        for (int i = 0; i < E_; i++) { int bi = y % P_; y /= P_; for (int r = 0; r < bi; r++) acc = FA[acc][ax]; ax = tx[ax]; }
        FM[a][b] = (uint8_t)acc;
    }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) if (FA[a][b] == 0) FN[a] = (uint8_t)b;
    for (int a = 1; a < q; a++) { int c = 0; for (int b = 1; b < q; b++) if (FM[a][b] == 1) { FI[a] = (uint8_t)b; c++; } if (c != 1) return 0; }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++)
        if (FM[a][FA[b][c]] != FA[FM[a][b]][FM[a][c]] || FM[FM[a][b]][c] != FM[a][FM[b][c]]) return 0;
    return 1;
}
static int det4z(uint8_t m[4][4]) {  /* 1 if the 4 x 4 matrix is singular */
    uint8_t a[4][4]; memcpy(a, m, 16);
    for (int c = 0; c < 4; c++) {
        int p = -1; for (int r = c; r < 4; r++) if (a[r][c]) { p = r; break; }
        if (p < 0) return 1;
        if (p != c) for (int j = 0; j < 4; j++) { uint8_t t = a[c][j]; a[c][j] = a[p][j]; a[p][j] = t; }
        for (int r = c + 1; r < 4; r++) if (a[r][c]) { uint8_t f = FM[a[r][c]][FI[a[c][c]]];
            for (int j = c; j < 4; j++) a[r][j] = FA[a[r][j]][FN[FM[f][a[c][j]]]]; }
    }
    return 0;
}
static int K, NR, NPR, NOR, PR[64], OR_[64]; static uint8_t *V;  /* V[(r*K+c)*4+j] */
#define VV(r, c) (V + (((size_t)(r) * K + (c)) * 4))
/* ---- PG(2,q) ---- */
static int NPT; static uint8_t PTV[1024][3]; static int PTIX[32 * 32 * 32];  /* normalized vector -> index */
static int (*THRU)[33];  /* lines through each point (q+1) */
static uint16_t *LINE2;  /* the line through two different points, NPT x NPT */
static int *MINLINE;     /* the smallest line through each point */
static int ptindex(const uint8_t w[3]) {
    int i = 0; while (i < 3 && !w[i]) i++;
    if (i == 3) return -1;
    uint8_t iv = FI[w[i]], n[3]; for (int j = 0; j < 3; j++) n[j] = FM[w[j]][iv];
    return PTIX[(n[0] * Q + n[1]) * Q + n[2]];
}
static int dot3(const uint8_t *a, const uint8_t *b) { return FA[FA[FM[a[0]][b[0]]][FM[a[1]][b[1]]]][FM[a[2]][b[2]]]; }
static void build_pg2(void) {
    NPT = 0;
    for (int a = 0; a < Q; a++) for (int b = 0; b < Q; b++) for (int c = 0; c < Q; c++) {
        uint8_t w[3] = {(uint8_t)a, (uint8_t)b, (uint8_t)c}; int i = 0; while (i < 3 && !w[i]) i++;
        if (i == 3 || w[i] != 1) { PTIX[(a * Q + b) * Q + c] = -1; continue; }
        memcpy(PTV[NPT], w, 3); PTIX[(a * Q + b) * Q + c] = NPT++;
    }
    THRU = malloc(sizeof(*THRU) * NPT);
    for (int p = 0; p < NPT; p++) { int n = 0; for (int l = 0; l < NPT; l++) if (!dot3(PTV[l], PTV[p])) THRU[p][n++] = l; if (n != Q + 1) { fprintf(stderr, "PG(2,q) error\n"); exit(4); } }
    /* tables: the unique line through two different points (verified incident with both), the least line through a point */
    LINE2 = malloc(sizeof(uint16_t) * (size_t)NPT * NPT); MINLINE = malloc(sizeof(int) * NPT);
    for (int p = 0; p < NPT; p++) { int m = THRU[p][0]; for (int i = 1; i <= Q; i++) if (THRU[p][i] < m) m = THRU[p][i]; MINLINE[p] = m; }
    for (int a = 0; a < NPT; a++) for (int b = 0; b < NPT; b++) {
        if (a == b) { LINE2[(size_t)a * NPT + b] = 0xFFFF; continue; }
        int L = -1, cnt = 0;
        for (int i = 0; i <= Q; i++) for (int j = 0; j <= Q; j++) if (THRU[a][i] == THRU[b][j]) { L = THRU[a][i]; cnt++; }
        if (cnt != 1 || dot3(PTV[L], PTV[a]) || dot3(PTV[L], PTV[b])) { fprintf(stderr, "PG(2,q) line table error\n"); exit(4); }
        LINE2[(size_t)a * NPT + b] = (uint16_t)L;
    }
}
/* quotient map per progression row: image of u_c in V/<u_0> as a point index, -1 for Z */
static int *IMG;  /* IMG[pi * K + c] */
static void quotient_images(int pi) {
    int r = PR[pi]; const uint8_t *u0 = VV(r, 0);
    int piv = 0; while (!u0[piv]) piv++;
    /* coordinates of V/<u0>: drop coordinate piv after eliminating it */
    uint8_t iv = FI[u0[piv]];
    for (int c = 0; c < K; c++) {
        const uint8_t *u = VV(r, c); uint8_t f = FM[u[piv]][iv], w[3]; int m = 0;
        for (int j = 0; j < 4; j++) if (j != piv) w[m++] = FA[u[j]][FN[FM[f][u0[j]]]];
        IMG[(size_t)pi * K + c] = ptindex(w);
    }
}
static int canon_line(int pi, int x, int y, int z) {  /* -2 if the triple does not fail this row */
    int p[3] = {IMG[(size_t)pi * K + x], IMG[(size_t)pi * K + y], IMG[(size_t)pi * K + z]}, d[3], nd = 0;
    for (int i = 0; i < 3; i++) if (p[i] >= 0) { int dup = 0; for (int j = 0; j < nd; j++) if (d[j] == p[i]) dup = 1; if (!dup) d[nd++] = p[i]; }
    if (nd == 0) return 0;
    if (nd == 1) return MINLINE[d[0]];
    int L = LINE2[(size_t)d[0] * NPT + d[1]];   /* the line through d0 and d1 */
    if (nd == 3 && dot3(PTV[L], PTV[d[2]])) return -2;
    return L;
}
typedef struct { int x, y, z; } tri_t;
typedef struct { int id; int **buf; int *path; tri_t *out; size_t nout, cap; unsigned long long listed; int lo, hi; } job_t;
static int NTH = 3, THR;
static int minline_through(int p) { int m = THRU[p][0]; for (int i = 1; i <= Q; i++) if (THRU[p][i] < m) m = THRU[p][i]; return m; }
static void emit(job_t *J, int x, int y, int z) {
    if (J->nout == J->cap) { J->cap = J->cap ? 2 * J->cap : 1024; J->out = realloc(J->out, J->cap * sizeof(tri_t)); }
    tri_t t = {x, y, z}; J->out[J->nout++] = t;
}
static int canon(int pi, int x, int y, int z) { return canon_line(pi, x, y, z); }  /* canon_line gives the least line for one point */
static void rec(job_t *J, int depth, int *S, int n) {
    if (depth == NPR || n <= THR) {
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) for (int c = b + 1; c < n; c++) {
            int x = S[a], y = S[b], z = S[c]; J->listed++;
            int ok = 1;
            for (int d = 0; d < depth && ok; d++) if (canon(d, x, y, z) != J->path[d]) ok = 0;
            for (int d = depth; d < NPR && ok; d++) if (canon_line(d, x, y, z) == -2) ok = 0;
            if (ok) { int s0 = x < y ? x : y; s0 = s0 < z ? s0 : z; int s2 = x > y ? x : y; s2 = s2 > z ? s2 : z; emit(J, s0, x + y + z - s0 - s2, s2); }
        }
        return;
    }
    /* bucket by the lines of row 'depth' through each column's image */
    int NL = NPT; int *cnt = calloc(NL + 1, sizeof(int));
    for (int i = 0; i < n; i++) { int p = IMG[(size_t)depth * K + S[i]]; if (p < 0) { for (int l = 0; l < NL; l++) cnt[l + 1]++; } else for (int j = 0; j <= Q; j++) cnt[THRU[p][j] + 1]++; }
    for (int l = 0; l < NL; l++) cnt[l + 1] += cnt[l];
    int *B = J->buf[depth]; int *fill = calloc(NL, sizeof(int));
    for (int i = 0; i < n; i++) { int p = IMG[(size_t)depth * K + S[i]];
        if (p < 0) { for (int l = 0; l < NL; l++) B[cnt[l] + fill[l]++] = S[i]; } else for (int j = 0; j <= Q; j++) { int l = THRU[p][j]; B[cnt[l] + fill[l]++] = S[i]; } }
    free(fill);
    for (int l = 0; l < NL; l++) {
        int m = cnt[l + 1] - cnt[l]; if (m < 3) continue;
        J->path[depth] = l;
        rec(J, depth + 1, B + cnt[l], m);
    }
    free(cnt);
}
static size_t BUFSZ;
static void *run(void *arg) {
    job_t *J = arg;
    /* the top level (row 0) is split by lines among threads */
    int NL = NPT; int *S0 = malloc(sizeof(int) * K); int n0;
    for (int l = J->id; l < NL; l += NTH) {
        n0 = 0;
        for (int c = 1; c < K; c++) { int p = IMG[c]; if (p < 0 || !dot3(PTV[l], PTV[p])) S0[n0++] = c; }
        if (n0 < 3) continue;
        J->path[0] = l; rec(J, 1, S0, n0);
    }
    free(S0); return NULL;
}
static int classify(int r) {  /* 1 progression, 0 other; A from the last independent columns */
    int sel[4], m = 0; uint8_t M[4][4];
    for (int c = K - 2; c >= 0 && m < 4; c--) {
        memcpy(M[m], VV(r, c), 4);
        /* independent of the chosen ones? rank test by elimination on a copy */
        uint8_t a[4][4]; memcpy(a, M, 16); int rank = 0;
        for (int col = 0; col < 4 && rank <= m; col++) { int p = -1; for (int i = rank; i <= m; i++) if (a[i][col]) { p = i; break; } if (p < 0) continue;
            if (p != rank) for (int j = 0; j < 4; j++) { uint8_t t = a[rank][j]; a[rank][j] = a[p][j]; a[p][j] = t; }
            for (int i = 0; i <= m; i++) if (i != rank && a[i][col]) { uint8_t f = FM[a[i][col]][FI[a[rank][col]]]; for (int j = 0; j < 4; j++) a[i][j] = FA[a[i][j]][FN[FM[f][a[rank][j]]]]; }
            rank++; }
        if (rank == m + 1) sel[m++] = c;
    }
    if (m < 4) return 0;
    /* solve A X = Y with X = [u_sel], Y = [u_sel+1]: rows of A from X^T a_i = y_i */
    uint8_t A[4][4];
    for (int i = 0; i < 4; i++) {
        uint8_t aug[4][5]; for (int j = 0; j < 4; j++) { for (int l = 0; l < 4; l++) aug[j][l] = VV(r, sel[j])[l]; aug[j][4] = VV(r, sel[j] + 1)[i]; }
        for (int col = 0; col < 4; col++) { int p = -1; for (int j = col; j < 4; j++) if (aug[j][col]) { p = j; break; } if (p < 0) return 0;
            if (p != col) for (int l = 0; l < 5; l++) { uint8_t t = aug[col][l]; aug[col][l] = aug[p][l]; aug[p][l] = t; }
            uint8_t iv = FI[aug[col][col]]; for (int l = 0; l < 5; l++) aug[col][l] = FM[aug[col][l]][iv];
            for (int j = 0; j < 4; j++) if (j != col && aug[j][col]) { uint8_t f = aug[j][col]; for (int l = 0; l < 5; l++) aug[j][l] = FA[aug[j][l]][FN[FM[f][aug[col][l]]]]; } }
        for (int l = 0; l < 4; l++) A[i][l] = aug[l][4];
    }
    if (det4z(A)) return 0;
    for (int c = 0; c + 1 < K; c++) for (int i = 0; i < 4; i++) {
        const uint8_t *u = VV(r, c); uint8_t s = 0; for (int l = 0; l < 4; l++) s = FA[s][FM[A[i][l]][u[l]]];
        if (s != VV(r, c + 1)[i]) return 0;
    }
    return 1;
}
int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IOLBF, 0);
    if (argc < 3) { fprintf(stderr, "usage: t4cells FAMILY q [threads]\n"); return 2; }
    if (!field(atoi(argv[2]))) { fprintf(stderr, "bad q\n"); return 2; }
    if (argc > 3) NTH = atoi(argv[3]);
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    char *line = NULL; size_t lc = 0; int cap = 0; V = NULL; K = -1; NR = 0; long q4 = (long)Q * Q * Q * Q;
    while (getline(&line, &lc, f) > 0) {
        if (line[0] == '#' || line[0] == '\n') continue;
        int n = 0; char *s = line, *e;
        for (;;) { long x = strtol(s, &e, 10); if (e == s) break; s = e;
            if (x < 0 || x >= q4) { fprintf(stderr, "bad entry\n"); return 2; }
            size_t need = ((size_t)NR * (K < 0 ? 1 : K) + n + 1) * 4;
            if (K < 0) need = ((size_t)n + 1) * 4 + ((size_t)NR) * 4;
            if ((long)need > cap) { cap = (int)(need * 2 + 4096); V = realloc(V, cap); }
            size_t at = ((size_t)NR * (K < 0 ? 0 : K) + n) * 4;
            V[at] = (uint8_t)(x / ((long)Q * Q * Q)); V[at + 1] = (uint8_t)(x / ((long)Q * Q) % Q); V[at + 2] = (uint8_t)(x / Q % Q); V[at + 3] = (uint8_t)(x % Q); n++; }
        if (K < 0) K = n; else if (n != K) { fprintf(stderr, "ragged\n"); return 2; }
        NR++;
    }
    fclose(f);
    NPR = NOR = 0;
    for (int r = 0; r < NR; r++) { if (classify(r)) PR[NPR++] = r; else OR_[NOR++] = r; }
    printf("t4cells %s: n = %d, k = %d, q = %d: %d progression rows, %d other rows\n", argv[1], NR, K, Q, NPR, NOR);
    if (!NPR) { printf("no progression rows\nRESULT FAIL\n"); return 3; }
    build_pg2();
    IMG = malloc(sizeof(int) * (size_t)NPR * K);
    for (int i = 0; i < NPR; i++) quotient_images(i);
    THR = 3 * Q; if (THR < 12) THR = 12;
    BUFSZ = (size_t)K * (NPT + 1);
    pthread_t th[64]; job_t *J = calloc(NTH, sizeof(job_t));
    for (int t = 0; t < NTH; t++) {
        J[t].id = t; J[t].buf = malloc(sizeof(int *) * 64); J[t].path = calloc(64, sizeof(int));
        /* bucket storage per depth: each column appears in q+1 buckets (Z columns in all) */
        for (int d = 0; d < 64; d++) J[t].buf[d] = NULL;
        for (int d = 1; d < NPR; d++) J[t].buf[d] = malloc(sizeof(int) * ((size_t)K * (Q + 1) + (size_t)K * 0 + 1024) * 2);
        pthread_create(&th[t], NULL, run, &J[t]);
    }
    size_t nrep = 0; tri_t *reps = NULL; unsigned long long listed = 0;
    for (int t = 0; t < NTH; t++) { pthread_join(th[t], NULL); reps = realloc(reps, (nrep + J[t].nout + 1) * sizeof(tri_t)); memcpy(reps + nrep, J[t].out, J[t].nout * sizeof(tri_t)); nrep += J[t].nout; listed += J[t].listed; }
    unsigned long long tested = 0, bad = 0; int lst = getenv("T4_LIST") != NULL; int shown = 0;
    for (size_t i = 0; i < nrep; i++) {
        int x = reps[i].x, y = reps[i].y, z = reps[i].z;
        for (int pi = 0; pi < NPR; pi++) { uint8_t m[4][4]; memcpy(m[0], VV(PR[pi], 0), 4); memcpy(m[1], VV(PR[pi], x), 4); memcpy(m[2], VV(PR[pi], y), 4); memcpy(m[3], VV(PR[pi], z), 4);
            if (!det4z(m)) { fprintf(stderr, "INTERNAL CHECK FAILED: 0 %d %d %d covered in a progression row\n", x, y, z); return 4; } }
        for (int a = 0; a + z < K; a++) {
            int cov = 0;
            for (int oi = 0; oi < NOR && !cov; oi++) { uint8_t m[4][4]; int r = OR_[oi]; memcpy(m[0], VV(r, a), 4); memcpy(m[1], VV(r, a + x), 4); memcpy(m[2], VV(r, a + y), 4); memcpy(m[3], VV(r, a + z), 4); if (!det4z(m)) cov = 1; }
            tested++;
            if (!cov) { bad++; if (lst || shown < 20) { printf("U %d %d %d %d\n", a, a + x, a + y, a + z); shown++; } }
        }
    }
    printf("triples listed in cells %llu; representatives {0,x,y,z} failing every progression row %zu (each once); shifts tested in the %d other rows %llu; uncovered %llu\n", listed, nrep, NOR, tested, bad);
    printf("%s\n", bad ? "RESULT FAIL" : "RESULT PASS");
    return bad ? 1 : 0;
}
