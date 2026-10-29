/* Resumable cyclic checks (scphf5_check, scphf6_check). With CHECK_PROGRESS=FILE the cyclic method writes one line
   per finished top-level normal (its own tallies: sets, failing sets, base sets, shifts tested, first failing set),
   after a header naming the array (FNV-1a hash of its bytes), q, the depth M and the number of normals. A later run
   on the same array with the same q, M and normals skips the normals already listed and adds their tallies, so a
   stopped check loses at most the normals in progress. Lines are rewritten through FILE.tmp on start; a partial
   last line (stopped while writing) or a header for another array is dropped. Without CHECK_PROGRESS nothing
   changes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

static FILE *PROG;
static char *PDONE;
static pthread_mutex_t PMX = PTHREAD_MUTEX_INITIALIZER;
static long long PSETS, PBAD, PBASE, PSHIFT;
static int PFIRST[6] = {-1, -1, -1, -1, -1, -1}, PRESUMED;

static uint64_t fnv_file(const char *path) {
    uint64_t h = 1469598103934665603ULL;
    FILE *f = fopen(path, "rb");
    if (!f) return 0;
    int c;
    while ((c = getc(f)) != EOF) { h ^= (unsigned char)c; h *= 1099511628211ULL; }
    fclose(f);
    return h;
}

static void progress_open(const char *array, int t, int q, int M, int NV, int W) {
    const char *pf = getenv("CHECK_PROGRESS");
    if (!pf || !*pf) return;
    char want[160], tmp[4096], line[512];
    snprintf(want, sizeof want, "scphf%d %016llx q %d M %d NV %d\n", t, (unsigned long long)fnv_file(array), q, M, NV);
    snprintf(tmp, sizeof tmp, "%s.tmp", pf);
    PDONE = calloc(NV, 1);
    FILE *out = fopen(tmp, "w");
    if (!out) { perror(tmp); exit(2); }
    fputs(want, out);
    FILE *in = fopen(pf, "r");
    if (in && fgets(line, sizeof line, in) && !strcmp(line, want)) {
        while (fgets(line, sizeof line, in)) {
            size_t len = strlen(line);
            if (!len || line[len - 1] != '\n') break;  /* partial last line */
            int i, f[6], used = 0;
            long long s, b, ba, sh;
            if (sscanf(line, "%d %lld %lld %lld %lld%n", &i, &s, &b, &ba, &sh, &used) != 5) break;
            int ok = 1;
            for (int x = 0; x < W && ok; x++) { int u = 0; ok = sscanf(line + used, "%d%n", &f[x], &u) == 1; used += u; }
            if (!ok || i < 0 || i >= NV || PDONE[i]) break;
            PDONE[i] = 1; PRESUMED++;
            PSETS += s; PBAD += b; PBASE += ba; PSHIFT += sh;
            if (f[0] >= 0 && PFIRST[0] < 0) memcpy(PFIRST, f, sizeof(int) * W);
            fputs(line, out);
        }
    }
    if (in) fclose(in);
    if (fclose(out) || rename(tmp, pf)) { perror(pf); exit(2); }
    PROG = fopen(pf, "a");
    if (!PROG) { perror(pf); exit(2); }
}

static void progress_line(int i, long long s, long long b, long long ba, long long sh, const int *first, int W) {
    if (!PROG) return;
    pthread_mutex_lock(&PMX);
    fprintf(PROG, "%d %lld %lld %lld %lld", i, s, b, ba, sh);
    for (int x = 0; x < W; x++) fprintf(PROG, " %d", first ? first[x] : -1);
    fputc('\n', PROG);
    fflush(PROG);
    pthread_mutex_unlock(&PMX);
}
