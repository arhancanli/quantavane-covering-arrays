/* t2pairs: exact check of an affine strength-2 covering perfect hash family in the ca-tools certificate format.
   Input: lines starting with '#' are comments; then n lines of k integers, each the vector (a, b) of GF(q)^2
   written as a*q + b. Affine means a = 1 everywhere. A pair of columns {i, j} is covered by row r when the
   vectors (1, b_r(i)) and (1, b_r(j)) are linearly independent, that is when b_r(i) != b_r(j) (the field codes
   are a bijection onto GF(q)). The program tests every one of the C(k, 2) pairs, row by row, and prints the
   number of pairs covered and the first uncovered pair if any. Exit 0 only when every pair is covered.
   Usage: t2pairs FAMILY q */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: t2pairs FAMILY q\n"); return 2; }
    int q = atoi(argv[2]);
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("open"); return 2; }
    size_t cap = 1 << 20, len = 0; int *vals = malloc(cap * sizeof(int));
    int n = 0; long k = -1;
    char *line = NULL; size_t lcap = 0; ssize_t got;
    while ((got = getline(&line, &lcap, f)) > 0) {
        if (line[0] == '#' || line[0] == '\n') continue;
        long cnt = 0; char *p = line, *e;
        for (;;) {
            long x = strtol(p, &e, 10);
            if (e == p) break;
            if (len == cap) { cap *= 2; vals = realloc(vals, cap * sizeof(int)); }
            vals[len++] = (int)x; cnt++; p = e;
        }
        if (k < 0) k = cnt; else if (cnt != k) { fprintf(stderr, "row %d has %ld entries, expected %ld\n", n, cnt, k); return 2; }
        n++;
    }
    fclose(f);
    printf("family %s: n = %d rows, k = %ld columns, q = %d\n", argv[1], n, k, q);
    /* affine and range check */
    for (size_t i = 0; i < len; i++) {
        int a = vals[i] / q, b = vals[i] % q;
        if (vals[i] < 0 || a != 1 || b < 0 || b >= q) {
            printf("NOT AFFINE: row %ld column %ld holds %d (a = %d)\nRESULT FAIL\n", (long)(i / k), (long)(i % k), vals[i], a);
            return 1;
        }
    }
    /* column-major copy of the points */
    unsigned char *pt = malloc((size_t)n * k);
    for (int r = 0; r < n; r++) for (long c = 0; c < k; c++) pt[(size_t)c * n + r] = (unsigned char)(vals[(size_t)r * k + c] - q);
    unsigned long long covered = 0, uncovered = 0; long fi = -1, fj = -1;
    for (long i = 0; i < k; i++) {
        const unsigned char *pi = pt + (size_t)i * n;
        for (long j = i + 1; j < k; j++) {
            const unsigned char *pj = pt + (size_t)j * n;
            int r = 0;
            while (r < n && pi[r] == pj[r]) r++;
            if (r < n) covered++;
            else { if (uncovered == 0) { fi = i; fj = j; } uncovered++; }
        }
    }
    unsigned long long expect = (unsigned long long)k * (unsigned long long)(k - 1) / 2;
    printf("pairs tested %llu (C(k,2) = %llu), covered %llu, uncovered %llu\n", covered + uncovered, expect, covered, uncovered);
    if (covered + uncovered != expect) { printf("COUNT MISMATCH\nRESULT FAIL\n"); return 3; }
    if (uncovered) { printf("first uncovered pair: %ld %ld\nRESULT FAIL\n", fi, fj); return 1; }
    printf("RESULT PASS: SCPHF(%d; %ld, %d, 2), CA(%d; 2, %ld, %d)\n", n, k, q, n * (q * q - q) + q, k, q);
    return 0;
}
