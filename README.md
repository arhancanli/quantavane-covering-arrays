# Covering arrays from Sherwood covering perfect hash families: families, checks and programs

196 Sherwood covering perfect hash families SCPHF(n; k, q, t), for prime powers 4 <= q <= 25 and strengths t = 3 to 6,
each giving a covering array CA(n(q^t - q) + q; t, k, q). 161 have at most 10,000 columns and 35 (strength 3) have more,
up to 100,000. Each family is in `families/` (listed in `families.csv`), with its exact check in `checks/` and the
checker in `checker/`. The programs that found the families, the closure and counting code behind the cell counts, and
the computations of the paper's subfield obstructions are in `code/` (see `code/README.md`).

Against the archival tables (Colbourn's tables of November 2024 with the order-seven sizes of Torres-Jimenez and
Izquierdo-Marquez 2024 and the strength-3 sizes of Shokri and Moura 2025), 153 of the 161 families give smaller
covering arrays, at 461,352 cells (t, v, k) with k <= 10,000 through the standard constructions, with the strength-6
family with q = 13 counted only on the 4,400 columns that two programs have checked (count of the revised paper;
`code/counting/v6/` has the list and the current count). Against Christopher Smolen's live ca-tools table of 2 November 2026
without our own rows, lowered by the later bounds listed below, 151 families improve 448,049 cells (`cells.csv`). Most
of these cells are reached through derivation, deleting symbols or doubling, and the savings range from marginal to
large; the paper gives the like-for-like comparisons. 185 of the families are VERIFIED in the ca-tools table by its own
exact check (five strength-6 families on a prefix of their columns only).

By Arhan Canli. The data (families, checks, tables) are under CC BY 4.0 (see LICENSE); the programs in `code/` are under
the MIT licence (see `code/LICENSE`).

Paper: A. Canli, Multiplicative rows in covering perfect hash families: subfield obstructions and exactly certified
covering arrays, manuscript, November 2026. First version: preprint, Zenodo,
31 October 2026, https://doi.org/10.5281/zenodo.23839216.

Two files in `families/` are not listed in `families.csv` and not counted: `CA_285212416_6_1000_16.cphf.txt` and
`CA_386200849_6_1000_17.cphf.txt`, strength-6 families with 1,000 columns superseded by the families with the same
numbers of rows and 5,000 columns (`CA_285212416_6_5000_16.cphf.txt`, `CA_386200849_6_5000_17.cphf.txt`).

## The construction

Each file in `families/` is a Sherwood covering perfect hash family: an n x k array whose entries are points of the
affine space AG(t-1, q), q a prime power, such that every set of t columns holds, in at least one row, t points that do
not lie on one hyperplane. By the theorem of Sherwood, Martirosyan and Colbourn (J. Combin. Des. 14 (2006) 202-213)
such a family gives a covering array CA(n(q^t - q) + q; t, k, q): for each row r and each affine function
u0 + u1 x1 + ... + u(t-1) x(t-1) that is not constant, write its value at each column's point in row r, and add the q
constant rows once.

File format: lines that start with a digit are the n rows of k point ids. A point (x1, ..., x(t-1)) has id
((x1 q + x2) q + ...) q + x(t-1); for a prime power q = p^e, a field element is its base-p digit vector (digit i is the
coefficient of x^i, modulo the polynomial named in the checker source). Other lines are comments.

## Checking a family

    cc -O3 -o scphf5_check checker/scphf5_check.c -lpthread
    ./scphf5_check 19 families/CA_17332579_5_720_19.cphf.txt

The strength-3 checker is `scphf_check.c`, then `scphf4_check.c`, `scphf5_check.c` and `scphf6_check.c`. Each tests
every set of t columns exactly (directly when C(k, t) is small enough; otherwise by an exact bucketing of the sets that
lie on one hyperplane in the first rows, or, for rows that are affine progressions v, Tv, T^2 v, ..., by the shift
argument described at the top of the source), then spot-checks random column sets of the expanded covering array.
The checkers were written separately from the searches that found the families. `checks/` holds their output for every
family, ending in PASS.

`scphf5_fast.c` and `scphf6_fast.c` (added 1 November 2026) are a second, faster exact implementation of the same shift
argument for strengths 5 and 6: each set that fails in every progression row is reached once from its first columns
after column 0, the remaining columns are classified per row by one table lookup, and every candidate is confirmed by
Gaussian elimination in the other rows. Their failing-set lists agree with brute force on test families, and they are
8 to 15 times faster than `scphf5_check.c` and `scphf6_check.c` on our families (for example the strength-5 family with
q = 23 and 10,000 columns in about 10 minutes on three threads).

## The improved cells

`cells.csv` has one row per cell improved against the live table: t, v, k, our bound N, the best bound before
("before"), the value the table lists ("table"), how the bound arises ("direct" from a named family with at least k
columns, or "derived" through the constructions below), and a note (`held`, see below). The list against the archival
baseline used in the paper is `code/counting/v6/data/arch_cells.csv.gz` (gzip; t, v, k, the table's own size, the closed
baseline "before", our size N, how it arises, and the source of the previous size), written by
`code/counting/v6_archival.py`.

"Before" in `cells.csv` is Smolen's live table (github.com/chrispbsmolen/ca-tools, commit ec6c172, 2 November 2026)
without our own rows. It holds the November 2024 copy of Charles Colbourn's covering array tables (the final one; the
tables stopped when he retired) together with later papers and verified arrays, and we lowered it by every other later
bound we found: Torres-Jimenez and Izquierdo-Marquez (Mathematics 12 (2024) 1908), Shokri, Moura and Stevens
(arXiv:2510.13122), Shokri's thesis (Ottawa, 2026) and Bergeron's strength-3 bounds
(github.com/MichelBacon/covering-arrays-rms-extension). Both sides are then closed under the same standard
constructions: a bound for k columns holds for fewer columns; an array over v symbols serves v - 1;
CAN(t-1, k-1, v) <= CAN(t, k, v) / v; the product construction for t = 2; and Roux's doubling for t = 3. A cell counts
only if the table lists it.

The `held` notes date from before Table 5.6 of Shokri's thesis had been compared; with its 39 strength-3 sizes added,
every cell in `cells.csv` remains improved. Eight of the 161 families improve no cell of the archival tables:
(t, q, n, k) = (5, 9, 17, 6560), (5, 11, 22, 10000) and (6, 19, 15, 1000) are dominated by other families of ours, and
(3, 7, 4, 234), (3, 7, 5, 619), (4, 7, 4, 62), (4, 7, 6, 207) and (4, 7, 7, 379) are matched or beaten by the
order-seven sizes of Torres-Jimenez and Izquierdo-Marquez. Against the live table two more improve nothing,
(5, 7, 26, 3000) and (5, 9, 16, 6560), which Smolen's cyclic families in that table beat.

## Entering the bounds in the ca-tools table

`ca-tools/rows.csv` gives the 277 bounds behind the improved cells in the table's own form: a row (t, v, k, N) says
that N runs suffice for up to k columns, and it improves the table from `k_from` to `k` (`cells` of them). Each row
names the family it comes from and the constructions applied after it (`steps`: `symbols to v=...`, an array over
v + 1 symbols serves v; `derive to t=...`, CAN(t-1, k-1, v) <= CAN(t, k, v) / v; or Roux's doubling), with the best
value the table listed before (`previous_best`, `previous_source`) and a `held` note (historical, see above). `ca-tools/add_rows.py`, run from the root of github.com/chrispbsmolen/ca-tools with the paper's DOI or
arXiv id, appends them to `table/ca_table.csv` as CITED rows, the way that repository's `tools/add_tjim7.py` enters the
order-seven sizes of Torres-Jimenez and Izquierdo-Marquez. It recomputes every previous best from the table and leaves
out any row that no longer improves it. (On a copy of the table at commit 392d8c9 it added all 279 rows of the
31 October version.) The ca-tools table took the families as checked certificates instead (ca-tools issue #5 and
the pull requests that followed); 185 are VERIFIED there.

## Strength 3 to 100,000 columns (4 November 2026)

34 Sherwood covering perfect hash families of strength 3 (n x k arrays of points of AG(2, q), affine rule
N = n(q^3 - q) + q) for q = 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23 and 25, each reaching k = 100,000 or a width on the
way (the ladder): together they give CA(N; 3, k, q) for every k from 10,001 to 100,000 at these twelve q. They were
grown column by column by `code/search/pq_cphf3big.c`, which never lists the pairs of old columns a new point spoils
while they are many. Each family was checked exactly twice, every column triple (about 1.7 x 10^14 triples at
k = 100,000): by checker/pq_scphf3_bigcheck.c in our own field coding, and again after conversion to the Conway-field
coding that ca-tools uses (checker/cphf_conway_check.py); both logs are in checks/ (`.scphf_check.out`,
`.conway_check.out`). The family files here are the certificates submitted to ca-tools, in its coding, with a one-line
header. The ca-tools table extended its strength-3 range to 100,000 columns for them (ca-tools issue #50).

## Strength 3, q = 4, n = 16 (released 7 November 2026)

`families/CA_964_3_90723_4.cphf.txt` is a Sherwood covering perfect hash family SCPHF(16; 90723, 4, 3), the missing
rung of the q = 4 ladder: it gives CA(964; 3, k, 4) for every k <= 90,723 (964 = 16(4^3 - 4) + 4), between the
n = 15 family (CA(904; 3, 49763, 4)) and the n = 17 family (CA(1024; 3, 100000, 4)). It was grown by
`code/search/pq_cphf3big.c` (run q4_n16, 3 November 2026 19:14 to 4 November 05:48, +04, when it stalled at 90,723
columns). The file is in the coding of the other strength-3 certificates (Conway coding, leading coordinate 1), with
the same two header lines. Three exact checks of every column triple (124,447,620,492,721 triples), each ending in PASS:

- `checks/CA_964_3_90723_4.scphf_check.out`: checker/pq_scphf3_bigcheck.c on the search output in our own coding;
- `checks/CA_964_3_90723_4.conway_check.out`: the same checker on this file;
- `checks/CA_964_3_90723_4.fullcheck3.out`: checker/fullcheck3.c, a second exact checker written separately from
  the searches and from pq_scphf3_bigcheck.c (Algorithm R from each largest column, every surviving pair confirmed by
  a determinant; a self-test against all triples of random arrays runs first), on this file.

The certificate for the ca-tools table, in the form of its pull request #51, is in
`ca-tools/submissions/canli-2026-11-t3-k90723/` (certificates.csv and the family file, byte for byte this one).

## Strength 6, q = 8: the 23-row family (released 7 November 2026)

`record/q8_n23_k4600/CA_6029136_6_4600_8.cphf.txt` is a draw of 23 multiplicative rows j -> a_r^j of GF(8^5), with
a_r = gamma^(e_r) (field polynomial, gamma and the exponents e_r in its header), on 4,600 columns. Its exact check by
`checker/scphf6_fast.c` (`CA_6029136_6_4600_8.scphf6_fast_check.out`, progress file
`CA_6029136_6_4600_8.scphf6_fast.progress`) found nine base sets uncovered by every row, the least with largest
column 3,171, so it is not a covering perfect hash family at 4,600 columns. Seven of the nine are the sets
151 * M that the paper proves to be uncovered by every multiplicative row of GF(8^5); the other two are covered by
some rows.

`families/CA_6029136_6_3171_8.cphf.txt` is its first 3,171 columns. Every set of six columns that no row covers is a
shift of one of the nine (the rows are progressions), so its least and largest columns differ by at least 3,171; the
first 3,171 columns therefore form an SCPHF(23; 3171, 8, 6), which gives CA(6,029,136; 6, 3171, 8)
(6,029,136 = 23(8^6 - 8) + 8). No strength-6 family of multiplicative rows over F_8 has more than 3,171 columns. The second
exact check, by the separately written `checker/fullcheck6.c` in mode full, passed on 8 November 2026: all
4,199,552,135,592 steps in 12 chunks on three Kaggle CPU sessions, no uncovered set (`checks/second/q8_3171_combine.txt`,
with each session's log in `checks/second/qv-fullcheck6-q8-3171-s1` to `-s3`). It enters `families.csv` and the cell
counts at the next recount; its certificate goes to the ca-tools table.

## Second checks of the strength-6 families

`checker/fullcheck6.c` is a second exact checker for strength-6 families of progression rows, written separately from
the searches and from `scphf6_check.c` and `scphf6_fast.c`: for a pair of columns x1 < x2 it reduces every row modulo
the span of the differences of x1, x2 and column 0 to points of PG(2, q), labels later columns by the lines through
the point of the largest column, groups them by their labels in four rows, tests each surviving pair in the other rows
and confirms it by a rank over F_p; its mode `tail` decides exactly the base sets whose largest column is at least a
given L. `checks/second/` holds its runs on the five 5,000-column families beyond the prefixes that the ca-tools table
checked (3,950, 4,200, 4,400, 4,800 and 4,900 columns): the plan (`plan.json`, chunks of the second column x1), the
results of every chunk (`*/results_*.jsonl`; Kaggle CPU sessions, and chunks 18 and 19 of q = 9 on our computer with
the same runner, `checker/fullcheck6_runner.py`) and the log of the local runs for q = 16 and 17. Verdicts:
`python3 -I checker/combine_fullcheck.py checks/second/plan.json checks/second/*/` gives "tail: PASS" for q = 9 and
q = 11 (and the log gives PASS for q = 16 and 17); for q = 13 the tail was not complete on 8 November 2026.

## Contact

Corrections are welcome as GitHub issues. The families have also been offered to the ca-tools table
(github.com/chrispbsmolen/ca-tools/issues/5).

## Exact checks on GitHub

`.github/workflows/verify.yml` checks one family exactly on GitHub's runners, in up to 20 parallel shards:
`checker/shards.py` splits the outer task x1 into ranges of about equal work, every shard runs
`checker/scphf5_fast.c` or `checker/scphf6_fast.c` on its range (`CHECK_TASKS`), and `checker/combine.py` accepts
the family only if every range ran once and no shard found a set of columns left uncovered. Run it from the Actions
tab or with `gh workflow run verify.yml -f family=families/NAME.cphf.txt -f q=Q -f t=T`.

