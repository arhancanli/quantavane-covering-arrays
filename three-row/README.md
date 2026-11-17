# Three rows, two copies of PG(2, q): CPHF(3; 2(q^2+q+1), q, 3) for q = 4^s (17 November 2026)

## The construction

Let q = 4^s, let c be a non-cube of GF(q) and b a root of X^3 - c in GF(q^3). Points of PG(2, q) are the elements
x of GF(q^3)^* / GF(q)^*, with GF(q^3) seen as GF(q)^3. The 3 x 2(q^2+q+1) array with columns

    B_x = (x, x^-1, x)      and      E_x = (x, b x^-1, b x)

is a covering perfect hash family CPHF(3; 2(q^2+q+1), q, 3): any three columns have a row whose three vectors are
linearly independent. By Sherwood, Martirosyan and Colbourn (J. Combin. Des. 14 (2006) 202-213) it gives
CA(3q^3 - 2; 3, k, q) for every k <= 2(q^2+q+1).

The B columns are the pair of Raaphorst, Moura and Stevens (Des. Codes Cryptogr. 73 (2014) 949-968). The cubic
X^3 - c over GF(2^(2m)) and the nucleus (0:1:0) also appear in Colbourn, Ingalls, Jedwab, Saaltink, Smith and Stevens
(Combin. Theory 4(1) (2024) #8), for orthogoval planes on one point set. At 2(q^2+q+1) columns the best general bound
before this was the 2-plication of Shokri and Moura, 4q^3 - 5q^2 + 2q (J. Combin. Des. 33 (2025) 156-171).

Proof in short. The inverses of the points u + v b of the line <1, b> are, in the basis (1, b, b^2), the points
(u^2 : -uv : v^2) of the conic X1^2 = X0 X2, because b^q = w b with w a cube root of unity. For two distinct such
points the determinant with b = (0, 1, 0) is (u1 v2 - u2 v1)(u1 v2 + u2 v1), which in characteristic 2 is the nonzero
square (u1 v2 + u2 v1)^2: b is the nucleus of that conic. Triples of B's or of E's are covered by rows 1-2 as in
Raaphorst-Moura-Stevens. For B, B, E or B, E, E, if rows 1 and 3 both fail, the span argument puts the three
row-2 entries, up to a common factor, at two points of that conic and at b, which are independent. A note with the
full proof is in preparation.

## Files

- families/CA_12286_3_546_16.cphf.txt: the family at q = 16, as 3 lines of 546 integers. Each integer is a vector of
  GF(16)^3 in base 16, most significant digit first. GF(16) = GF(2)[x]/(x^4 + x + 1) with codes c0 + 2c1 + 4c2 + 8c3
  (the Conway coding of ca-tools). Coordinates are in the basis (1, b, b^2) of GF(16)[b]/(b^3 - x).
  Columns 1-273 are B_x and columns 274-546 are E_x, for the 273 points in the same order.
- code/kummer_dump.c and code/to_rows.py rebuild that file byte for byte:
  `cc -O2 -o kd kummer_dump.c && ./kd 4 0 dump.txt && python3 to_rows.py dump.txt out.txt`
  (r = 4, so q = 2^4).
- code/kummer3.c: check 1. It uses GF(q)[b]/(b^3 - c) and 3 x 3 determinants. The map x -> g x multiplies each row by a
  fixed field element, so it tests every triple through B_1 or E_1. `./kummer3 r` for q = 2^r; `./kummer3 r 1` is a
  red control.
- code/singer.h, code/singer_check.c and code/singer_check2.c: check 2, written separately. Points are Singer exponents
  of a primitive element of another cubic, and collinearity comes from a planar difference set (a line table, or for
  large q a difference table). `./singer_check q`, `NO_LINE_TABLE=1 ./singer_check2 q`; a second argument 1 is a red
  control.
- code/cphf_filecheck.c: a brute force over every triple of a family file in the one-column-per-line layout of
  kummer_dump. It has its own GF(2^r) and GF(p) arithmetic.

## Checks (17 November 2026)

- checks/q4_q16_q64.txt: checks 1 and 2 at q = 4, 16 and 64 PASS, and every red control FAILS.
- checks/q256_kummer3.txt and checks/q256_singer_check2.txt: q = 256 PASS with both checks, 1.73e10 triples each.
- checks/cphfcheck_q16_keeper_tool.txt: the ca-tools checker tools/cphf/cphfcheck.c, mode full, on the q = 16 file.
  It checks 26,979,680 t-sets with 0 uncovered, and gives CA(12286; 3, 546, 16). A file with one entry changed leaves
  152 uncovered.
