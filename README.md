# New upper bounds for covering array numbers, strengths 3 to 6

150 covering perfect hash families give covering arrays CA(N; t, k, v) smaller than the best known sizes, for
strengths t = 3 to 6, v = 4 to 25 and up to k = 10,000 columns. Together, through the standard constructions, they
lower 397,782 cells of the covering array tables. Each family is in `families/`, with the exact check of it in
`checks/` and the checker in `checker/`.

By Arhan Canli. Data and code under CC BY 4.0 (see LICENSE).

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

"Before" is the November 2024 copy of Charles Colbourn's covering array tables (the final one; the tables stopped when
he retired), lowered by every later bound we found: Torres-Jimenez and Izquierdo-Marquez (Mathematics 12 (2024) 1908),
Shokri, Moura and Stevens (arXiv:2510.13122), Shokri's thesis (Ottawa, 2026), Bergeron's strength-3 bounds
(github.com/MichelBacon/covering-arrays-rms-extension), and the table at chrispbsmolen.github.io/ca-tools as of
29 October 2026. Both sides are then closed under the same standard constructions: a bound for k columns holds for
fewer columns; an array over v symbols serves v - 1; CAN(t-1, k-1, v) <= CAN(t, k, v) / v; the product construction
for t = 2; and Roux's doubling for t = 3. A cell counts only if the table lists it.

1,845 strength-3 cells (v = 4 to 9, k = 241 to 4672) are marked `held` until we have compared them with Table 5.6 of
Shokri's thesis, which we could not read yet.

## Contact

Corrections are welcome as GitHub issues. The families have also been offered to the ca-tools table
(github.com/chrispbsmolen/ca-tools/issues/5).
