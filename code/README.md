# Code: the searches that produced the families, and the counts

This folder holds the programs that produced the 196 families listed in `families.csv` and the code behind the
paper's counts of improved table cells.

- `search/`: the search programs, in every revision that produced a released family.
- `counting/`: the closure under standard constructions, its input tables, and the scripts that count improved cells.
- `PROVENANCE.csv`: for each of the 196 families, the program, the source revision and the run that produced it.
- `subfield/`: the computations behind the paper's subfield obstructions and exact widths of families of
  multiplicative rows (Theorem 4.5 and Section S7 of its supporting information).

## Licence and authorship

The code in this folder (`code/`) is released under the MIT licence (`code/LICENSE`). The data in the rest of the
repository (the families, check logs, checkers, `cells.csv`, `families.csv` and the top-level README) stay under
CC BY 4.0, as stated in the top-level `LICENSE`. The two input tables in `counting/` list published bounds with
their sources; cite those sources when you use them (one table is transcribed from a thesis released under CC BY-SA
4.0).

All programs in this folder were written with an AI system (Claude, by Anthropic) under the direction of the
author, Arhan Canli.

## search/

Each program prints a first line `best k K (q Q, n N, ...)`, then the array: n lines of k point ids. The output is a
Sherwood covering perfect hash family SCPHF(n; k, q^(t-1), t); by Sherwood, Martirosyan and Colbourn (2006) it gives
a covering array CA(n(q^t - q) + q; t, k, q). The checkers are in `checker/` (CC BY 4.0).

| file | engine revision | what it does | families (last run) |
|---|---|---|---|
| `cphf3_v1.c` | 8c2a30e | t = 3: grows columns one at a time; depth-first choice of the new column's point in each row; random column drops when stuck | 4 |
| `cphf3_v2.c` | b9ff365 | as v1, plus least-conflict swaps, incremental pair lists, up to 8,192 columns (the paper's "cphf3 (v2)") | 6 (and the first run of 5 more) |
| `cphf3x_v1.c` | bbe66c6 | t = 3 for many columns: lists only the pairs of old columns that a first-row point spoils, from line incidence | 2 (and the first run of 16 more) |
| `cphf3x_v2.c` | 29b1861 | v1 plus `CPHF_START=FILE`: continue from an earlier array; the search itself is unchanged | 26 |
| `cphf4x_v1.c` | 9860888 | t = 4 over AG(3,q): triples listed per first-row plane, determinant tests | 13 (and the first run of 6 more) |
| `cphf4x_v2.c` | 29b1861 | v1 plus `CPHF_START` | 27 |
| `cphf4m.c` | ab23744 | t = 4 for up to 10,000 columns: old columns bucketed by the lines through their directions from the new point; greedy later rows | 29 |
| `cphf5m.c` | da73271 | t = 5, column by column, as cphf4m one dimension up | 24 |
| `cphf5c_v1.c` | 4eeb174 | t = 5, partly cyclic: the first C rows are progressions of points (powers in GF(q^4), or of GF(q^3) x GF(q)), the rest random; only shifts of the sets through column 0 that fail in every cyclic row are tested against the random rows | 6 |
| `cphf5c_v2.c` | 79d2f5c | v1 plus a mode for small q, where no row reaches order K (rows of the largest order of each type, repeating within K columns), and a corrected count of shifted sets | 1 |
| `cphf5l_v1.c` | uncommitted (built 2026-11-01 00:48 +04) | low-memory form of cphf5c: failing sets kept once, packed or streamed; mixed row types; last rows by local search | 1 |
| `cphf5l_v2.c` | uncommitted (built 2026-11-01 01:36 +04) | v1 with a column sweep in the local search and the `CPHF_LSROWS` option | 1 |
| `cphf5l_v3.c` | 2bf74ba | v2 with one bound changed: after a failed attempt, the rows tested in the stream grow up to n - C - `CPHF_LSROWS` (as in v2 at the default, 1) | 1 |
| `cphf6c_v1.c` | 386a9fe | t = 6, partly cyclic: C rows of powers in GF(q^5), the rest random | 1 |
| `cphf6c_v2.c` | a861e63 | v1 plus a pure cyclic mode: with C = n every row is a progression gamma^(e j), no search | 19 |
| `cphf6p` | a861e63 | shell wrapper: `cphf6p q n seconds seed K` runs `cphf6c q n seconds seed K n` | (the 10 runs it made are counted under cphf6c_v2) |
| `pq_cphf3big_v1.c` | uncommitted (built 2026-11-03 17:10 +04) | t = 3 to 100,000 columns in little memory: no pair lists; old columns classed by direction from the new point, O(k) per row | 3 |
| `pq_cphf3big_v2.c` | uncommitted (built 2026-11-03 17:35 +04) | v1 with cheaper scoring of candidate points, sampled scoring where full scoring costs too much, wider branching above the exact last rows, and new options | 2 (and the first run of 1 more) |
| `pq_cphf3big_v3.c` | 62ea2eb | v2 with branching over the last random row and new default settings | 30 |

"Last run" counts each family once, by the program of the run that wrote it. 28 families were grown in two runs: a
second run continued from the first run's array (`CPHF_START`, `PQ_START`); `PROVENANCE.csv` lists both.

### Build

Any C99 compiler with POSIX threads. The runs used these commands (Apple clang 21, macOS, arm64):

    cc -O3 -o cphf3x cphf3x_v2.c                        # likewise cphf3_v2, cphf3x_v1, cphf4x_*, cphf4m, cphf5m (-lm)
    clang -O3 -mcpu=native -o cphf3 cphf3_v1.c
    cc -O3 -o cphf5c cphf5c_v1.c -lm -lpthread           # likewise cphf5c_v2, cphf5l_*, cphf6c_*
    cc -O3 -march=native -o pq_cphf3big pq_cphf3big_v3.c -lm

Every file here also compiles without warnings with `cc -O2 ... -lm -lpthread` (checked 7 Nov 2026).

### Run

    ./cphf3 q n seconds seed [maxk] [tries] [maxviol]            # cphf3_*, cphf3x_* (cphf3_v1: no maxviol);
                                                                  # cphf3x_v2: CPHF_START=FILE continues
    ./cphf4x q n seconds seed [maxk] [tries] [maxviol]           # cphf4x_* (v2: CPHF_START); cphf4m, cphf5m: [maxk] [tries]
    ./cphf5c q n seconds seed K [C]                               # cphf6c likewise; CPHF_THREADS sets threads
    ./cphf5l q n seconds seed K C1 C2 [R1]
    ./pq_cphf3big q n maxk cpu_seconds seed OUT [stall_seconds] [maxviol] [tries]   # PQ_START=FILE continues

`seconds` is a CPU-time budget. The exact command line of every released family is in `PROVENANCE.csv`, for example
`cphf6c 9 21 10 5 5000 21` for `families/CA_11160081_6_5000_9.cphf.txt`. The searches are randomized and stop on CPU
time, so a rerun with the recorded seed need not stop at the same array. The 19 pure cyclic strength-6 families do
not depend on time: rerunning `cphf6c_v2.c` with their recorded arguments reproduced all 19 files byte for byte
(7 Nov 2026). The check logs of every family are in `checks/`.

### How the provenance was found

Each family file was matched, by its rows, to an output of the search engine (the author's private repository).
The queue log gives each run's command line and start time; the time each binary was built and the engine's commit
history give the source revision that the run used. Checks:

- The machine code (text section) of the last build of every program equals that of a rebuild of the committed
  source listed above.
- The earlier builds of cphf3x, cphf4x, cphf5c and cphf6c were made in the same command as their commit, or with no
  recorded edit between build and commit.
- Four builds were never committed: `cphf5l_v1.c`, `cphf5l_v2.c`, `pq_cphf3big_v1.c` and `pq_cphf3big_v2.c`. Their
  sources were recovered by replaying, in order, every recorded write and edit of the file up to the build. Continued
  to the end, the same replay gives the committed files (2bf74ba, 62ea2eb) byte for byte.

In `PROVENANCE.csv`, `program` names the file in `search/` (last run first; earlier runs follow after ` <- `),
`source_commit` the engine revision ("uncommitted" for the four builds above), and `run_or_seed` the command line as
run, with its start time (+04) and CPU seconds. Binary names of the time: `cphf3` = `cphf3_v1.c`, `cphf3v2` =
`cphf3_v2.c`, `cphf6p` = `cphf6c` with C = n.

### Programs not included

No released family came from these, so they are not here: `cphf3m` (engine 274dcef, a strength-3 search with
direction buckets, used for test runs only); the cphf3 revision 83bd416 (least-conflict swaps, used for one 60-second
comparison); and the cphf5c revisions da73271 and 386a9fe (no queued run used them).

## counting/

| file | what it is |
|---|---|
| `ca_tables.py` | dense tables of bounds on CAN(t,k,v) (t 2-6, v 2-25, k <= 20,000) and their closure under the standard constructions: fewer columns, symbol deletion, derivation, strength-2 product, Roux doubling |
| `v4_archival.py` | every count against the archival baseline (Tables 1-3, S1, S4, S5; the cells that rest on the authors' checks) |
| `rich_recount.py` | the same counts under a richer closure, and against the live table |
| `dependent_cells.py` | the cells that rest only on the full-width checks of five strength-6 families |
| `recount_v2.py` | the count against the live table with later bounds, and its agreement with `cells.csv` |
| `prior_methods.py` | which construction held the previous value of each improved cell |
| `ca_later.tsv` | 329 bounds published after the November 2024 copy of Colbourn's tables, each line t, v, k, N and its source: Torres-Jimenez and Izquierdo-Marquez, Mathematics 12 (2024) 1908, Tables 4-7 (152 lines); github.com/MichelBacon/covering-arrays-rms-extension, improvements.csv (78); rows of github.com/chrispbsmolen/ca-tools, table of 28-29 Oct 2026 (79); Shokri, PhD thesis, Ottawa 2026, doi:10.20381/ruor-31663, and Shokri, Moura and Stevens, arXiv:2510.13122 (20). Compiled 28-29 Oct 2026. |
| `shokri_thesis_table56.tsv` | Table 5.6 of Shokri's thesis (CC BY-SA 4.0), transcribed 6 Nov 2026; `recount_v2.py` recomputes every size from the thesis' formulas before use |

Not included: the ca-tools table itself (github.com/chrispbsmolen/ca-tools; the scripts read `table/ca_table.csv` at
commits ce719cb and ec6c172, and `rich_recount.py` also `table/derived.csv` and `r/livingtable/data/dcan_table.csv`
at ce719cb), and Colbourn's `colbournBigFrame.csv`, which only `ca_tables.load()` uses; no counting script calls it.

Requirements: Python 3 with numpy (tested with Python 3.9.6, numpy 2.0.2), git, a clone of this repository that
contains commit ea668c0 (the scripts read `families.csv` and `cells.csv` there with `git show`), and a full clone of
ca-tools. From the repository root:

    git clone https://github.com/chrispbsmolen/ca-tools.git ../ca-tools
    OUT=/tmp/out python3 code/counting/v4_archival.py . ../ca-tools        # about 15 s
    OUT=/tmp/out python3 code/counting/rich_recount.py . ../ca-tools       # also dependent_cells.py, recount_v2.py, prior_methods.py

Outputs go to `$OUT` (default `./out`). The scripts differ from the paper's copies only in import paths, file
locations and the docstrings that named them. Run from this release on 7 Nov 2026, `v4_archival.py` printed the 123
lines of the paper's log and wrote five output files identical to the paper's copies; the other four scripts
reproduced their logs exactly.

`dependent_v5.py` (added for the current version of the paper) counts the cells that rest on the authors' checks
alone, given which second checks are complete: from the repository root,
`python3 code/counting/dependent_v5.py . ../ca-tools STATUS.json OUT.json`, where `STATUS.json` is the
`second_checks_status.json` of the paper's supporting information. It reproduces the 461,352 archival cells of
`v4_archival.py`.

## subfield/

The paper's Theorem 4.3 decides whether the columns wM (w = D_1(q)/D_1(r), q = r^g, gcd(g, d) = 1) are covered by a
multiplicative row of GF(q^d), or by none, through linear algebra over F_r in K = GF(r^d). These programs apply it.

| file | what it does |
|---|---|
| `usearch.c` | `usearch p f d g W`: every M with 0 in M, max M <= W, \|M\| = d + 1, decided by the criterion (one beta per Frobenius orbit of PG(d-1, r), r = p^f); prints the M for which wM is uncovered by every multiplicative row |
| `usearch2.c` | the same list, faster: solves for one element of M by linear algebra and a discrete-logarithm table instead of enumerating it; progress lines `done max W'`; `PRIM=1` restricts beta to primitive classes (Conjecture 4.6) |
| `explore.py` | a separate Python implementation of the criterion, used to cross-check the two programs |
| `crosscheck.sh` | runs the three implementations on 11 cases and compares their lists |
| `allrows2.c` | `allrows2 e d W`, q = 2^e: every (d+1)-set within the first W + 1 columns decided directly over all rows a^j of GF(q^d) (one per class {a^(2^i)}) |
| `direct_q4.py` | checks the criterion against direct computation in GF(4^5) on all 142,506 candidate sets 11M |
| `test_criterion_a.py` | randomized comparison of Theorem 4.3(a) with direct computation in GF(q^3) for q = 9 and 25 |
| `check_arc_d3.py` | numerical check of Theorem 4.8(a): for d = 3, no three points theta^s are collinear for both theta and theta^-1 |
| `run_subfield.sh` | runs all of them; `sh run_subfield.sh all` adds the long runs (q = 9, 16 and 25, hours on a shared machine) |

Build: `cc -O2 -o usearch usearch.c` (likewise `usearch2`, `allrows2`); the Python scripts need only the standard
library.

