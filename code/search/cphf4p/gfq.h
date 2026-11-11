/* GF(q), q <= 25 prime or 4, 8, 9, 16, 25, in the ca-tools coding: an element of GF(p^e) is the integer
   sum c_i p^i of its coordinates in the basis 1, x, ..., x^(e-1) of GF(p)[x]/(f), f the Conway polynomial
   (x^2+x+1, x^3+x+1, x^4+x+1, x^2+2x+2, x^2+4x+2). Field axioms are verified on every triple at start. */
#ifndef GFQ_H
#define GFQ_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
static int GQ, GP, GE;
static uint8_t GADD[32][32], GSUB[32][32], GMUL[32][32], GINV[32], GNEG[32];
static int gf_init(int q) {
    GQ = q; GP = 0;
    for (int d = 2; d <= q; d++) if (q % d == 0) { GP = d; break; }
    GE = 0; for (int x = 1; x < q; x *= GP) GE++;
    { int x = 1; for (int i = 0; i < GE; i++) x *= GP; if (x != q || q > 32) return 0; }
    int f[6] = {0};
    if (GE == 2 && GP == 2) { f[0] = 1; f[1] = 1; }
    else if (GE == 3 && GP == 2) { f[0] = 1; f[1] = 1; }
    else if (GE == 4 && GP == 2) { f[0] = 1; f[1] = 1; }
    else if (GE == 2 && GP == 3) { f[0] = 2; f[1] = 2; }
    else if (GE == 2 && GP == 5) { f[0] = 2; f[1] = 4; }
    else if (GE != 1) return 0;
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int ca[6], cb[6], s = 0, d = 0, pw = 1, u = a, w = b;
        for (int i = 0; i < GE; i++) { ca[i] = u % GP; u /= GP; cb[i] = w % GP; w /= GP; }
        for (int i = 0; i < GE; i++) { s += ((ca[i] + cb[i]) % GP) * pw; d += ((ca[i] - cb[i] + GP) % GP) * pw; pw *= GP; }
        GADD[a][b] = (uint8_t)s; GSUB[a][b] = (uint8_t)d;
        int pr[12] = {0};
        for (int i = 0; i < GE; i++) for (int j = 0; j < GE; j++) pr[i + j] = (pr[i + j] + ca[i] * cb[j]) % GP;
        for (int dd = 2 * GE - 2; dd >= GE; dd--) { int c = pr[dd]; pr[dd] = 0; if (!c) continue;
            for (int i = 0; i < GE; i++) pr[dd - GE + i] = ((pr[dd - GE + i] - c * f[i]) % GP + GP) % GP; }
        s = 0; pw = 1; for (int i = 0; i < GE; i++) { s += pr[i] * pw; pw *= GP; }
        GMUL[a][b] = (uint8_t)s;
    }
    for (int a = 0; a < q; a++) GNEG[a] = GSUB[0][a];
    GINV[0] = 0;
    for (int a = 1; a < q; a++) { int c = 0; for (int b = 1; b < q; b++) if (GMUL[a][b] == 1) { GINV[a] = (uint8_t)b; c++; } if (c != 1) return 0; }
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++)
        if (GMUL[a][GADD[b][c]] != GADD[GMUL[a][b]][GMUL[a][c]] || GMUL[GMUL[a][b]][c] != GMUL[a][GMUL[b][c]] ||
            GADD[GADD[a][b]][c] != GADD[a][GADD[b][c]] || GADD[a][b] != GADD[b][a] || GMUL[a][b] != GMUL[b][a]) return 0;
    return 1;
}
/* rank of m vectors of GF(q)^4 (m <= 4), each given as 4 bytes */
static int gf_rank4(const uint8_t v[][4], int m) {
    uint8_t a[4][4]; for (int i = 0; i < m; i++) for (int j = 0; j < 4; j++) a[i][j] = v[i][j];
    int r = 0;
    for (int col = 0; col < 4 && r < m; col++) {
        int piv = -1; for (int i = r; i < m; i++) if (a[i][col]) { piv = i; break; }
        if (piv < 0) continue;
        if (piv != r) for (int j = 0; j < 4; j++) { uint8_t t = a[r][j]; a[r][j] = a[piv][j]; a[piv][j] = t; }
        uint8_t iv = GINV[a[r][col]];
        for (int i = 0; i < m; i++) if (i != r && a[i][col]) {
            uint8_t fct = GMUL[a[i][col]][iv];
            for (int j = 0; j < 4; j++) a[i][j] = GSUB[a[i][j]][GMUL[fct][a[r][j]]];
        }
        r++;
    }
    return r;
}
#endif
