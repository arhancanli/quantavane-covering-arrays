/* Reading a strength-4 CPHF in the ca-tools certificate format: '#' lines are comments, then n lines of k
   integers, each the vector (u0, u1, u2, u3) of GF(q)^4 written in base q, most significant digit first. */
#ifndef FAMIO_H
#define FAMIO_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { int n; long k; uint8_t *u; } fam_t;  /* u[((size_t)r * k + c) * 4 + j] */
static int fam_read(const char *path, int q, fam_t *F) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); return 0; }
    char *line = NULL; size_t cap = 0; long k = -1; int n = 0; size_t ucap = 0; uint8_t *u = NULL;
    while (getline(&line, &cap, f) > 0) {
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') continue;
        long cnt = 0; char *s = line, *e;
        for (;;) {
            long x = strtol(s, &e, 10); if (e == s) break; s = e;
            if (x < 0 || x >= (long)q * q * q * q) { fprintf(stderr, "entry %ld out of range in row %d\n", x, n); return 0; }
            size_t need = ((size_t)n * (k < 0 ? 1 : k) + cnt + 1) * 4;
            if (k < 0) need = ((size_t)cnt + 1) * 4;
            if (need > ucap) { ucap = need * 2 + 4096; u = realloc(u, ucap); }
            size_t base = (k < 0 ? (size_t)cnt : (size_t)n * k + cnt) * 4;
            u[base + 0] = (uint8_t)(x / (q * q * q)); u[base + 1] = (uint8_t)(x / (q * q) % q);
            u[base + 2] = (uint8_t)(x / q % q); u[base + 3] = (uint8_t)(x % q);
            cnt++;
        }
        if (k < 0) k = cnt; else if (cnt != k) { fprintf(stderr, "row %d has %ld entries, expected %ld\n", n, cnt, k); return 0; }
        n++;
    }
    fclose(f); free(line);
    F->n = n; F->k = k; F->u = u; return n > 0;
}
#define UV(F, r, c) ((F)->u + (((size_t)(r) * (F)->k + (c)) * 4))
#endif
