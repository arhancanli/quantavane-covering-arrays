/* export_orbit.c -- write the 2-orbit array (g, a g + u_j, b g + v_j) as GF(q)^3 coordinate vectors (prime q only),
   one column per line "r1 r2 r3" with each entry "x0,x1,x2" (coordinates of alpha^i in the basis 1, X, X^2).
   usage: export_orbit q a b u v > file */
#include "singer.h"
int main(int argc, char **argv) {
    int q = atoi(argv[1]), A = atoi(argv[2]), B = atoi(argv[3]), u = atoi(argv[4]), v = atoi(argv[5]);
    if (!setup_singer(q) || Rdeg != 1) return 2;
    int (*vec)[3] = malloc(sizeof(int[3]) * N); int cur[3] = {1, 0, 0}, nx[3];
    for (int i = 0; i < N; i++) { vec[i][0] = cur[0]; vec[i][1] = cur[1]; vec[i][2] = cur[2]; mul3(cur, ALPHA, nx); cur[0] = nx[0]; cur[1] = nx[1]; cur[2] = nx[2]; }
    for (int j = 0; j < 2; j++) for (int g = 0; g < N; g++) {
        int p[3] = { g, (int)(((long)A * g + (j ? u : 0)) % N), (int)(((long)B * g + (j ? v : 0)) % N) };
        for (int t = 0; t < 3; t++) printf("%d,%d,%d%c", vec[p[t]][0], vec[p[t]][1], vec[p[t]][2], t < 2 ? ' ' : '\n');
    }
    return 0;
}
