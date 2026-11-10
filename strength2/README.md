# Strength 2: families of all n-tuples (10 November 2026)

Nine Sherwood covering perfect hash families of strength 2 are kept here, one folder each, for the prime powers 8, 9,
11, 13, 16, 17, 19, 23 and 25. In each family the columns are the first k of the q^n n-tuples of GF(q) in
lexicographic order, and every point x of AG(1, q) is written as the vector (1, x) of GF(q)^2, the integer q + x. Any
two columns differ in some row, so by the theorem of Sherwood, Martirosyan and Colbourn (J. Combin. Des. 14 (2006)
202-213) the family gives CA(n(q^2 - q) + q; 2, k, q). The array is the classical n-fold direct product of the affine
plane's orthogonal array OA(q^2; q, q, 2), so nothing here is new as a construction. These families are entered in the
ca-tools covering array table for the widths past 20,000, where its strength-2 rows stop.

| folder | family | array |
|---|---|---|
| [CA_288_2_32768_8](CA_288_2_32768_8/) | SCPHF(5; 32768, 8, 2) | CA(288; 2, 32,768, 8) |
| [CA_369_2_59049_9](CA_369_2_59049_9/) | SCPHF(5; 59049, 9, 2) | CA(369; 2, 59,049, 9) |
| [CA_561_2_100000_11](CA_561_2_100000_11/) | SCPHF(5; 100000, 11, 2) | CA(561; 2, 100,000, 11) |
| [CA_637_2_28561_13](CA_637_2_28561_13/) | SCPHF(4; 28561, 13, 2) | CA(637; 2, 28,561, 13) |
| [CA_976_2_65536_16](CA_976_2_65536_16/) | SCPHF(4; 65536, 16, 2) | CA(976; 2, 65,536, 16) |
| [CA_1105_2_83521_17](CA_1105_2_83521_17/) | SCPHF(4; 83521, 17, 2) | CA(1,105; 2, 83,521, 17) |
| [CA_1387_2_100000_19](CA_1387_2_100000_19/) | SCPHF(4; 100000, 19, 2) | CA(1,387; 2, 100,000, 19) |
| [CA_2047_2_100000_23](CA_2047_2_100000_23/) | SCPHF(4; 100000, 23, 2) | CA(2,047; 2, 100,000, 23) |
| [CA_2425_2_100000_25](CA_2425_2_100000_25/) | SCPHF(4; 100000, 25, 2) | CA(2,425; 2, 100,000, 25) |

Each folder holds the family (`.cphf.txt`, the file submitted to ca-tools), its ca-tools certificate row
(`certificates.csv`), `HOW.md` (the construction and the one-line program that writes the file), and three check logs:

- `checker/t2pairs.c`: every one of the C(k, 2) pairs of columns, tested row by row (exact);
- `checker/t2distinct.py`, written separately: the k column tuples are pairwise distinct (exact, the same condition);
- `checker/t2expand.c`: the expanded covering array itself, with its own field arithmetic, every pair of columns in two
  windows of 1,500 columns (the first and a random one) showing all q^2 pairs of symbols.

Red controls (a duplicated column, an entry not of the form (1, x), a one-digit change that makes two columns equal)
fail both exact checks, and a duplicated column fails the window check.
