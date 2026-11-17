/* cphf_filecheck.c -- checks a CPHF(n; k, q, 3) FILE over GF(p) (p prime) or GF(2^r) by brute force over EVERY triple
   of columns (no symmetry). Field arithmetic written here from scratch: GF(2^r) by shift-and-add multiplication modulo
   the given polynomial, GF(p) by integers mod p. (family-theorems lane, 17 Nov 2026; separate from kummer3.c,
   singer_check*.c and cphf_brute.py.)  usage: cphf_filecheck FILE p|2^r [poly_hex]   e.g. cphf_filecheck f 16 13 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int Q, P2 = 0, POLY = 0, R = 0;
static int add(int a, int b) { return P2 ? (a ^ b) : (a + b) % Q; }
static int sub(int a, int b) { return P2 ? (a ^ b) : (a - b + Q) % Q; }
static int mul(int a, int b) {
    if (!P2) return a * b % Q;
    int r = 0; while (b) { if (b & 1) r ^= a; b >>= 1; a <<= 1; if (a & Q) a ^= POLY; } return r;
}
static int det(int *u, int *v, int *w) {
    int t1 = sub(mul(v[1], w[2]), mul(v[2], w[1])), t2 = sub(mul(v[0], w[2]), mul(v[2], w[0])), t3 = sub(mul(v[0], w[1]), mul(v[1], w[0]));
    return add(sub(mul(u[0], t1), mul(u[1], t2)), mul(u[2], t3));
}
int main(int argc, char **argv) {
    Q = atoi(argv[2]); if (argc > 3) { P2 = 1; POLY = (int)strtol(argv[3], 0, 16); }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    static int col[4000][4][3]; int k = 0, n = -1; char line[4096];
    while (fgets(line, sizeof line, f)) {
        int m = 0; char *p = strtok(line, " \n");
        while (p) { if (sscanf(p, "%d,%d,%d", &col[k][m][0], &col[k][m][1], &col[k][m][2]) != 3) return 2;
            for (int i = 0; i < 3; i++) if (col[k][m][i] < 0 || col[k][m][i] >= Q) return 2;
            m++; p = strtok(NULL, " \n"); }
        if (m == 0) continue; if (n < 0) n = m; else if (m != n) return 2; k++;
    }
    long long bad = 0, tot = 0;
    for (int a = 0; a < k; a++) for (int b = a + 1; b < k; b++) for (int c = b + 1; c < k; c++) { tot++;
        int ok = 0; for (int r = 0; r < n && !ok; r++) if (det(col[a][r], col[b][r], col[c][r])) ok = 1;
        if (!ok) bad++; }
    printf("%s: k %d rows %d q %d triples %lld uncovered %lld -> %s\n", argv[1], k, n, Q, tot, bad, bad ? "FAIL" : "PASS");
    return bad ? 1 : 0;
}
