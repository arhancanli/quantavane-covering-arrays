# Strength 4 at 100,000 columns (11 November 2026)

Four covering perfect hash families of strength 4, CPHF(n; 100000, q, 4), found by our search with
`code/search/cphf4p/t4ref_v1.c` and `t4ref_v2.c`, one folder each. By the theorem of Sherwood, Martirosyan and Colbourn
(2006) each gives a covering array CA(n(q^4 - 1) + 1; 4, 100000, q). The vectors are not all affine, so the expansion
is the general one. They are entered in the ca-tools covering array table, where strength 4 has no row past 10,000
columns.

| folder | family | array | progression / other rows | representatives | built by |
|---|---|---|---|---|---|
| [CA_7031233_4_100000_25](CA_7031233_4_100000_25/) | CPHF(18; 100000, 25, 4) | CA(7,031,233; 4, 100,000, 25) | 14 / 4 | 142,068 | t4ref_v1, seed 2, 1 thread |
| [CA_4757281_4_100000_23](CA_4757281_4_100000_23/) | CPHF(17; 100000, 23, 4) | CA(4,757,281; 4, 100,000, 23) | 14 / 3 | 23,640 | t4ref_v1, seed 1, 4 threads |
| [CA_2345761_4_100000_19](CA_2345761_4_100000_19/) | CPHF(18; 100000, 19, 4) | CA(2,345,761; 4, 100,000, 19) | 14 / 4 | 431,451 | t4ref_v1, seed 1, 4 threads |
| [CA_1753921_4_100000_17](CA_1753921_4_100000_17/) | CPHF(21; 100000, 17, 4) | CA(1,753,921; 4, 100,000, 17) | 16 / 5 | 1,710,598 | t4ref_v2, seed 1, 1 thread |

The families are partly cyclic (Canli 2026, doi:10.5281/zenodo.23839216). Most rows are progressions u_(c+1) = M u_c:
- Singer rows multiply by a primitive element of GF(q^4);
- affine rows are a^j in GF(q^3);
- affine rows are (b^j, j) in GF(q^2) x GF(q).

In a progression row four columns fail exactly when their shift to column 0 does. So the search lists the
"representatives", the sets {0, x, y, z} that fail in every progression row. It then draws random rows to cover all
of their shifts, and repairs the last random row by local search. `t4ref_v2.c` differs from v1 only in that repair: it
allows sideways moves, so it does not stall on a plateau. Each family's second comment line lists its rows and
polynomials; its `HOW.md` gives the exact command.

Checks, as of 11 November 2026:
- `t4ref` in mode check, our refinement checker: PASS for all four. It lists every representative, so the counts add up to C(k - 1, 3), rechecks each by rank, and tests every shift in the other rows.
- ca-tools `tools/cphf/cphfcheck.c` in mode progression, the table's own checker: PASS for all four, every t-set covered.
- `checker/t4cells.c`, our cells checker, written separately: not finished. At 100,000 columns it needs more than 37 core-hours per family (a run on another 18-row family for q = 23 stopped unfinished after 9.4 hours on 4 threads), so its logs will be added here only when a run completes.

The ca-tools certificate workflow runs its own exact check after each pull request is merged.
