# New upper bounds for covering array numbers, strengths 3 to 6

155 covering perfect hash families give covering arrays CA(N; t, k, v) smaller than the best known sizes, for
strengths t = 3 to 6, v = 4 to 25 and up to k = 10,000 columns. Together, through the standard constructions, 143 of
them lower 401,649 cells of the covering array tables (the live ca-tools table on 1 November 2026, plus later papers).
Each family is in `families/`, with the exact check of it in `checks/` and the checker in `checker/`. The 277 bounds
that give these cells are in `ca-tools/rows.csv`, ready to enter in the ca-tools table (see below).

By Arhan Canli. Data and code under CC BY 4.0 (see LICENSE).

Paper: A. Canli, New upper bounds for covering array numbers from partly cyclic covering perfect hash families,
preprint, Zenodo, 31 October 2026, https://doi.org/10.5281/zenodo.23839216 (Table 2 lists the 279 bounds).

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

## The improved cells

`cells.csv` has one row per improved cell: t, v, k, our bound N, the best bound before ("before"), the value the table
lists ("table"), and how the bound arises ("direct" from a named family with at least k columns, or "derived" through
the constructions below). `families.csv` lists the families with their parameters.

"Before" is Christopher Smolen's live table at chrispbsmolen.github.io/ca-tools (commit 29a9344, 1 November 2026),
which holds the November 2024 copy of Charles Colbourn's covering array tables (the final one; the tables stopped when
he retired) together with later papers and verified arrays, lowered by every other later bound we found:
Torres-Jimenez and Izquierdo-Marquez (Mathematics 12 (2024) 1908), Shokri, Moura and Stevens (arXiv:2510.13122),
Shokri's thesis (Ottawa, 2026) and Bergeron's strength-3 bounds (github.com/MichelBacon/covering-arrays-rms-extension).
Both sides are then closed under the same standard constructions: a bound for k columns holds for
fewer columns; an array over v symbols serves v - 1; CAN(t-1, k-1, v) <= CAN(t, k, v) / v; the product construction
for t = 2; and Roux's doubling for t = 3. A cell counts only if the table lists it.

1,845 strength-3 cells (v = 4 to 9, k = 241 to 4672) are marked `held` until we have compared them with Table 5.6 of
Shokri's thesis, which we could not read yet. Twelve families improve no cell on their own any more: six with q = 7
are matched or beaten by the order-seven bounds of Torres-Jimenez and Izquierdo-Marquez and by the cyclic families in
the ca-tools table; two with q = 9 and 6,560 columns (16 and 17 rows, found 1 November) are beaten by a 15-row family
with 7,381 columns entered in the ca-tools table the same day; and three strength-6 families with 1,000 columns and a
22-row family with q = 11 are superseded by our families with more columns or fewer rows.

## Entering the bounds in the ca-tools table

`ca-tools/rows.csv` gives the 277 bounds behind the improved cells in the table's own form: a row (t, v, k, N) says
that N runs suffice for up to k columns, and it improves the table from `k_from` to `k` (`cells` of them). Each row
names the family it comes from and the constructions applied after it (`steps`: `symbols to v=...`, an array over
v + 1 symbols serves v; `derive to t=...`, CAN(t-1, k-1, v) <= CAN(t, k, v) / v; or Roux's doubling), with the best
value the table listed before (`previous_best`, `previous_source`) and a `held` note where Shokri's Table 5.6 still has
to be read. `ca-tools/add_rows.py`, run from the root of github.com/chrispbsmolen/ca-tools with the paper's DOI or
arXiv id, appends them to `table/ca_table.csv` as CITED rows, the way that repository's `tools/add_tjim7.py` enters the
order-seven sizes of Torres-Jimenez and Izquierdo-Marquez. It recomputes every previous best from the table and leaves
out any row that no longer improves it. (On a copy of the table at commit 392d8c9 it added all 279 rows of the
31 October version.) The ca-tools table prefers checked certificates for families like these; that route is being
prepared with its maintainer (ca-tools issue #5).

## Contact

Corrections are welcome as GitHub issues. The families have also been offered to the ca-tools table
(github.com/chrispbsmolen/ca-tools/issues/5).
