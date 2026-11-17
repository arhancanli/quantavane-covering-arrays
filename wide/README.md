# Strength 3 past 100,000 columns, and alphabets 27 and above (8 November 2026; four larger families 11 November 2026; alphabet 41, 16 November 2026)

Sherwood covering perfect hash families of strength 3 are kept here, one folder each: twenty from 8 and 11 November, and those of 16 November listed in the last two sections. Twelve take the ladders
of q = 4 to 25 past 100,000 columns, up to 408,135. Eight are over the alphabets 27, 29, 31 and 32: four with six rows
(8 November) and four with seven rows that reach 534,635 to 944,542 columns (11 November, see below). One is over the
alphabet 41 with seven rows and 643,825 columns (16 November, see below). All of them lie
outside the scope of the ca-tools covering array table, which keeps strengths 2 to 6, alphabets up to 25 and widths
up to 100,000 (Christopher Smolen, ca-tools issue #54, 7 November 2026). So the table does not list them, and we keep
them here.

Each family is an n x k array of points of the affine plane AG(2, q), every vector with first coordinate 1. By the
theorem of Sherwood, Martirosyan and Colbourn (J. Combin. Des. 14 (2006) 202-213) it gives
CA(n(q^3 - q) + q; 3, k, q). By Lemma 3.1 of Colbourn, Keri, Rivas Soriano and Schlage-Puchta (Discrete Appl. Math.
158 (2010) 1158-1180), fusing m symbols then gives CA(n(q^3 - q) + q - 2m; 3, k, q - m) for every smaller alphabet.

## The families and the cells they fill

A cell is a strength, alphabet and width (3, v, k). Below, a cell is listed when all three of these hold, and it is counted
only when, in addition, no published construction or bound we found beats it (categories (a) and (t) of "Which cells
count" below):

- the ca-tools table has no entry for it today (k above 100,000 at v up to 25; any k above 25);
- the family, or its fused array, gives an array there;
- the constructions of the ca-tools derived lookup give no smaller size there. We ran tools/derive_table.py from ca-tools at commit ce719cb on a copy of the table, with these families and their fused arrays added and its ladder of widths continued past 100,000.

That lookup has no baseline above 25, and it does not cover every published construction. So on 16 November 2026 we
compared every family, width by width, with the published constructions and bounds we could find (see "Which cells
count" below). That check replaces what this paragraph used to say: the cut-off q(q^2 + q + 1) and the claim that the
construction of Shokri and Moura gives "about 3% fewer rows" there were wrong. For odd q their (q+1)-plication reaches
(q + 1)(q^2 + q + 1) columns, and at q = 27 it has about 20% fewer rows than our six-row family, not 3%.

In all, the families give 124,688,057 cells (3, q, k) at their own alphabets past every table. Of these, 89,594,748
are not beaten by any published construction or bound we found, and only these are counted: 81,501,744 where our
array is smaller than every published construction we found (category (a), the only ones we call records) and
8,093,004 where a published existence bound gives an array of the same size (category (t), a tie). The other
35,093,309 are beaten by published work and are not counted: 25,707,682 by explicit constructions (category (b);
all 18,140,165 cells of the alphabet-193 family are here) and 9,385,627 by a published existence method (category
(b*)). The categories of each family are in the table "Which cells count" below. Cells reached by fusing symbols
(5,713,735 from the families of 8 and 11 November) are not counted; of the 1,039,275 of them at prime-power alphabets
that we checked, 702,142 are beaten by published constructions. Published constructions we did not find or could not
read could still beat some cells of category (a) or (t).

| folder | family | array | widths past the tables at v = q | cells by fusing |
|---|---|---|---|---|
| [CA_1024_3_165004_4](CA_1024_3_165004_4/) | SCPHF(17; 165004, 4^2, 3) | CA(1,024; 3, 165,004, 4) | 65,004 (k 100,001 to 165,004) | none |
| [CA_1685_3_154375_5](CA_1685_3_154375_5/) | SCPHF(14; 154375, 5^2, 3) | CA(1,685; 3, 154,375, 5) | 54,375 (k 100,001 to 154,375) | none |
| [CA_3703_3_137618_7](CA_3703_3_137618_7/) | SCPHF(11; 137618, 7^2, 3) | CA(3,703; 3, 137,618, 7) | 37,618 (k 100,001 to 137,618) | v = 6: 37,618 (CA(3,701; 3, k, 6), k 100,001 to 137,618) |
| [CA_5048_3_116455_8](CA_5048_3_116455_8/) | SCPHF(10; 116455, 8^2, 3) | CA(5,048; 3, 116,455, 8) | 16,455 (k 100,001 to 116,455) | none |
| [CA_7209_3_221150_9](CA_7209_3_221150_9/) | SCPHF(10; 221150, 9^2, 3) | CA(7,209; 3, 221,150, 9) | 121,150 (k 100,001 to 221,150) | none |
| [CA_11891_3_207658_11](CA_11891_3_207658_11/) | SCPHF(9; 207658, 11^2, 3) | CA(11,891; 3, 207,658, 11) | 107,658 (k 100,001 to 207,658) | v = 10: 107,658 (CA(11,889; 3, k, 10), k 100,001 to 207,658) |
| [CA_17485_3_134368_13](CA_17485_3_134368_13/) | SCPHF(8; 134368, 13^2, 3) | CA(17,485; 3, 134,368, 13) | 34,368 (k 100,001 to 134,368) | v = 12: 34,368 (CA(17,483; 3, k, 12), k 100,001 to 134,368) |
| [CA_32656_3_322146_16](CA_32656_3_322146_16/) | SCPHF(8; 322146, 16^2, 3) | CA(32,656; 3, 322,146, 16) | 222,146 (k 100,001 to 322,146) | v = 14: 222,146 (CA(32,652; 3, k, 14), k 100,001 to 322,146); v = 15: 222,146 (CA(32,654; 3, k, 15), k 100,001 to 322,146) |
| [CA_34289_3_106533_17](CA_34289_3_106533_17/) | SCPHF(7; 106533, 17^2, 3) | CA(34,289; 3, 106,533, 17) | 6,533 (k 100,001 to 106,533) | none |
| [CA_47899_3_160839_19](CA_47899_3_160839_19/) | SCPHF(7; 160839, 19^2, 3) | CA(47,899; 3, 160,839, 19) | 60,839 (k 100,001 to 160,839) | v = 17: 35,839 (CA(47,895; 3, k, 17), k 125,001 to 160,839); v = 18: 60,839 (CA(47,897; 3, k, 18), k 100,001 to 160,839) |
| [CA_85031_3_302074_23](CA_85031_3_302074_23/) | SCPHF(7; 302074, 23^2, 3) | CA(85,031; 3, 302,074, 23) | 202,074 (k 100,001 to 302,074) | v = 20: 202,074 (CA(85,025; 3, k, 20), k 100,001 to 302,074); v = 21: 202,074 (CA(85,027; 3, k, 21), k 100,001 to 302,074); v = 22: 202,074 (CA(85,029; 3, k, 22), k 100,001 to 302,074) |
| [CA_109225_3_408135_25](CA_109225_3_408135_25/) | SCPHF(7; 408135, 25^2, 3) | CA(109,225; 3, 408,135, 25) | 308,135 (k 100,001 to 408,135) | v = 20: 106,061 (CA(109,215; 3, k, 20), k 302,075 to 408,135); v = 21: 106,061 (CA(109,217; 3, k, 21), k 302,075 to 408,135); v = 22: 106,061 (CA(109,219; 3, k, 22), k 302,075 to 408,135); v = 23: 106,061 (CA(109,221; 3, k, 23), k 302,075 to 408,135); v = 24: 308,135 (CA(109,223; 3, k, 24), k 100,001 to 408,135) |
| [CA_117963_3_108143_27](CA_117963_3_108143_27/) | SCPHF(6; 108143, 27^2, 3) | CA(117,963; 3, 108,143, 27) | 87,704 (k 20,440 to 108,143) | v = 26: 87,704 (CA(117,961; 3, k, 26), k 20,440 to 108,143) |
| [CA_146189_3_135764_29](CA_146189_3_135764_29/) | SCPHF(6; 135764, 29^2, 3) | CA(146,189; 3, 135,764, 29) | 110,505 (k 25,260 to 135,764) | v = 26: 27,621 (CA(146,183; 3, k, 26), k 108,144 to 135,764); v = 27: 27,621 (CA(146,185; 3, k, 27), k 108,144 to 135,764); v = 28: 110,505 (CA(146,187; 3, k, 28), k 25,260 to 135,764) |
| [CA_178591_3_167721_31](CA_178591_3_167721_31/) | SCPHF(6; 167721, 31^2, 3) | CA(178,591; 3, 167,721, 31) | 136,938 (k 30,784 to 167,721) | v = 26: 31,957 (CA(178,581; 3, k, 26), k 135,765 to 167,721); v = 27: 31,957 (CA(178,583; 3, k, 27), k 135,765 to 167,721); v = 28: 31,957 (CA(178,585; 3, k, 28), k 135,765 to 167,721); v = 29: 31,957 (CA(178,587; 3, k, 29), k 135,765 to 167,721); v = 30: 136,938 (CA(178,589; 3, k, 30), k 30,784 to 167,721) |
| [CA_196448_3_184913_32](CA_196448_3_184913_32/) | SCPHF(6; 184913, 32^2, 3) | CA(196,448; 3, 184,913, 32) | 151,089 (k 33,825 to 184,913) | v = 26: 17,192 (CA(196,436; 3, k, 26), k 167,722 to 184,913); v = 27: 17,192 (CA(196,438; 3, k, 27), k 167,722 to 184,913); v = 28: 17,192 (CA(196,440; 3, k, 28), k 167,722 to 184,913); v = 29: 17,192 (CA(196,442; 3, k, 29), k 167,722 to 184,913); v = 30: 17,192 (CA(196,444; 3, k, 30), k 167,722 to 184,913); v = 31: 17,192 (CA(196,446; 3, k, 31), k 167,722 to 184,913) |
| [CA_137619_3_534635_27](CA_137619_3_534635_27/) | SCPHF(7; 534635, 27^2, 3) | CA(137,619; 3, 534,635, 27) | 349,722 (k 184,914 to 534,635) | v = 26: 349,722 (CA(137,617; 3, k, 26), k 184,914 to 534,635) |
| [CA_170549_3_684678_29](CA_170549_3_684678_29/) | SCPHF(7; 684678, 29^2, 3) | CA(170,549; 3, 684,678, 29) | 499,765 (k 184,914 to 684,678) | v = 26: 150,043 (CA(170,543; 3, k, 26), k 534,636 to 684,678); v = 27: 150,043 (CA(170,545; 3, k, 27), k 534,636 to 684,678); v = 28: 499,765 (CA(170,547; 3, k, 28), k 184,914 to 684,678) |
| [CA_208351_3_860049_31](CA_208351_3_860049_31/) | SCPHF(7; 860049, 31^2, 3) | CA(208,351; 3, 860,049, 31) | 675,136 (k 184,914 to 860,049) | v = 26 to 29: 175,371 each (CA(208,341 + 2(v - 26); 3, k, v), k 684,679 to 860,049); v = 30: 675,136 (CA(208,349; 3, k, 30), k 184,914 to 860,049) |
| [CA_229184_3_944542_32](CA_229184_3_944542_32/) | SCPHF(7; 944542, 32^2, 3) | CA(229,184; 3, 944,542, 32) | 759,629 (k 184,914 to 944,542) | v = 26 to 31: 84,493 each (CA(229,172 + 2(v - 26); 3, k, v), k 860,050 to 944,542) |
| [CA_354349_3_647632_37](CA_354349_3_647632_37/) | SCPHF(7; 647632, 37^2, 3) | CA(354,349; 3, 647,632, 37) | 595,573 (k 52,060 to 647,632) | not counted |
| [CA_482201_3_643825_41](CA_482201_3_643825_41/) | SCPHF(7; 643825, 41^2, 3) | CA(482,201; 3, 643,825, 41) | 573,182 (k 70,644 to 643,825) | not counted |

## The four families of 11 November 2026

Four families with seven rows, grown by the same program from our 100,000-column seven-row families (runs q27_n7_k1m,
q29_n7_k1m, q31_n7_k1m and q32_n7_k1m, seeds 2027, 2029, 2031 and 2032, 7 November 2026), checked exactly three times
like the others. They take the alphabets 26 to 32, where the ca-tools table has no entries at all, from 184,913 columns
(the widest of the families above) to 944,542: for each alphabet v and width k, the counted array is the one from the
smallest q >= v whose family reaches k, fused when v < q. That gives 759,629 new cells at each of the seven alphabets,
5,317,403 in all (2,284,252 at the families' own alphabets, 3,033,151 by fusing). Between 108,144 and 184,913 columns
they also give smaller arrays than the ones listed above at the alphabets 26 to 29 (251,838 cells already counted,
not counted again). Two notes on their files: the third check's log records a self-test run separately after the check,
and its local folder prefix was removed from the log; the ca-tools certificate rows for these four families are not
written yet.

## Alphabets 37 and above (16 November 2026)

Families over a prime alphabet q from 37 to 61 with seven rows, grown from nothing (no start family) by
`code/search/pq_cphf3big_v4.c`, which is `pq_cphf3big_v3.c` with MAXQ 32 -> 64 and MAXK 1,000,000 -> 4,000,000 (two
lines), seed 1000 + q, 40,000 CPU seconds at most. Each family is checked by `checker/pq_scphf3_bigcheck_q64.c` on the
search output and by `checker/fullcheck3_q64.c` on the family file: the repository's two checkers with MAXQ 32 -> 64
(one line each). For a prime q the Conway field is GF(q) itself, so there is no separate Conway check. A cell (3, q, k)
is listed only at the family's own alphabet q and only for k above q(q^2 + q + 1) (a cut-off we used then; the
categories of "Which cells count" decide which widths count); the ca-tools table has no entries above alphabet 25.
Fused cells are not counted here.

The families over q = 37 and 41 (their rows are in the table above) are the search's checkpoints at about 9,800 and 9,662 CPU seconds (the runs were stopped then; seeds 1037 and 1041). With it, the families
here give 4,580,025 cells at their own alphabets.

## Families made of group orbits (16 November 2026)

These families are unions of orbits of a group G = Z_M1 x Z_M2 that acts on every row by an invertible 2 x 2 matrix
over GF(q): multiplication by an element of norm 1 of GF(q^2), the point (x, y) read as x + y w with w^2 the least
non-residue mod q. The file `NAME.orbit.txt` holds, in the ca-tools coding, the representatives (n rows), and in its
header the two matrices G1 and G2 of every row with their orders M1 and M2. The family is
{ (G1_r^i G2_r^j c_r)_r : c a representative, 0 <= i < M1, 0 <= j < M2 }, column t M1 M2 + i M2 + j
(`checker/expand_orbit.py` writes it out in full).

Why checking the triples that contain a representative is enough: an invertible linear map sends three distinct,
non-collinear points to three distinct, non-collinear points and back, so G maps covered triples to covered triples.
G maps the family onto itself, and the column G1^i G2^j c of any triple goes to c under G1^(M1 - i) G2^(M2 - j). So
every triple of the family is the image of a triple that contains a representative, and is covered exactly when that
one is.

Each family is checked by two programs, each of which verifies the group itself (every matrix invertible and sending
every line onto a line, G1 G2 = G2 G1, G1^M1 = G2^M2 = I in every row), expands the family with its own code, counts
its columns distinct, and decides every triple that contains a representative:

- `checker/pq_scphf3orb_checkA.c`, from `pq_scphf3_bigcheck.c` (each representative takes the place of the largest
  column, with all other columns as members; determinant confirmation and the covering-array spot check kept), on
  the search output;
- `checker/fullcheck3orb.c`, from `fullcheck3.c` (Algorithm R from each representative over all other columns;
  expansion by matrix powers; distinctness by sorting), on `NAME.orbit.txt`.

Before any family here was counted, the new and the old checkers were run side by side: the old ones on full
expansions of orbit families at q = 7, 13, 19 and 41 (149,940 columns at q = 41, every one of its C(k, 3) triples),
the new ones on the compact files; all PASS, and red controls (a duplicated representative, a changed entry, a broken
matrix) failed in each program that could see them. The two new checkers report the same number of uncovered triples
on every red and random file whose group is valid, and fullcheck3orb's self-test matches brute force.

For alphabets above 127 the version-2 programs are used: `code/search/pq_cphf3orb2.c` (no table of size q^4; the
same families as pq_cphf3orb for the same seed at q = 13 to 109), `checker/pq_scphf3orb_checkA2.c` (labels per
representative) and `checker/fullcheck3orb2.c` (MAXQ 256), the same counts as version 1 on every test file; at q = 193
they and `checker/fullcheck3_q256.c` (fullcheck3 with MAXQ 256) on the full expansion all PASS a 56,454-column family
(29,985,398,669,204 triples), and version 2 fails its red control. Their covering-array spot check uses 50 samples
there (its cost grows as q^3).

Found by `code/search/pq_cphf3orb.c` (pq_cphf3big v4 with the group added; with the trivial group it reproduces v4
byte for byte). The widths listed per family below are those past every table and above any narrower family of ours at that q; which
of them count is in the table "Which cells count". Fused cells are not counted. That a search used a group is not
new (automorphisms are a standard aid in covering-array search); the arrays and their widths are the results.

| folder | family | array | widths past the tables at v = q |
|---|---|---|---|
| [CA_9064549_3_15996200_109](CA_9064549_3_15996200_109/) | SCPHF(7; 15996200, 109^2, 3), 2644 orbits of Z_110 x Z_55 | CA(9,064,549; 3, 15,996,200, 109) | 14,689,181 (k 1,307,020 to 15,996,200) |
| [CA_6388129_3_13008618_97](CA_6388129_3_13008618_97/) | SCPHF(7; 13008618, 97^2, 3), 2709 orbits of Z_98 x Z_49 | CA(6,388,129; 3, 13,008,618, 97) | 12,086,439 (k 922,180 to 13,008,618) |
| [CA_2722681_3_10998546_73](CA_2722681_3_10998546_73/) | SCPHF(7; 10998546, 73^2, 3), 4017 orbits of Z_74 x Z_37 | CA(2,722,681; 3, 10,998,546, 73) | 10,604,127 (k 394,420 to 10,998,546) |
| [CA_50322241_3_25366664_193](CA_50322241_3_25366664_193/) | SCPHF(7; 25366664, 193^2, 3), 1348 orbits of Z_194 x Z_97 | CA(50,322,241; 3, 25,366,664, 193) | 18,140,165 (k 7,226,500 to 25,366,664) |
| [CA_1588501_3_9757994_61](CA_1588501_3_9757994_61/) | SCPHF(7; 9757994, 61^2, 3), 5077 orbits of Z_62 x Z_31 | CA(1,588,501; 3, 9,757,994, 61) | 9,527,231 (k 230,764 to 9,757,994) |
| [CA_2104939_3_9609828_67](CA_2104939_3_9609828_67/) | SCPHF(7; 9609828, 67^2, 3), 8313 orbits of Z_68 x Z_17 | CA(2,104,939; 3, 9,609,828, 67) | 9,304,509 (k 305,320 to 9,609,828) |
| [CA_9064549_3_33994950_109](CA_9064549_3_33994950_109/) | SCPHF(7; 33994950, 109^2, 3), 5619 orbits of Z_110 x Z_55 | CA(9,064,549; 3, 33,994,950, 109) | 17,998,750 (k 15,996,201 to 33,994,950) |
| [CA_354349_3_1751572_37](CA_354349_3_1751572_37/) | SCPHF(7; 1751572, 37^2, 3), 2426 orbits of Z_38 x Z_19 | CA(354,349; 3, 1,751,572, 37) | 1,103,940 (k 647,633 to 1,751,572) |
| [CA_556291_3_2908356_43](CA_556291_3_2908356_43/) | SCPHF(7; 2908356, 43^2, 3), 6009 orbits of Z_44 x Z_11 | CA(556,291; 3, 2,908,356, 43) | 2,826,957 (k 81,400 to 2,908,356) |
| [CA_6388129_3_27995660_97](CA_6388129_3_27995660_97/) | SCPHF(7; 27995660, 97^2, 3), 5830 orbits of Z_98 x Z_49 | CA(6,388,129; 3, 27,995,660, 97) | 14,987,042 (k 13,008,619 to 27,995,660) |
| [CA_2722681_3_19242664_73](CA_2722681_3_19242664_73/) | SCPHF(7; 19242664, 73^2, 3), 7028 orbits of Z_74 x Z_37 | CA(2,722,681; 3, 19,242,664, 73) | 8,244,118 (k 10,998,547 to 19,242,664) |

## Which cells count (16 November 2026)

For each family (n rows over the alphabet q, so N = n(q^3 - q) + q rows in the covering array) and each width k past
the tables, we compared N with these published routes, in this order:

- (b) an explicit published construction with fewer rows reaches k: the (q+1)-plication of Shokri and Moura (J.
  Combin. Des. 33(4) (2025); read through Shokri's 2026 thesis, chapter 5), for odd prime powers q, with
  6q^3 - (13q^2 - 5q)/2 - 1 rows up to (q + 1)(q^2 + q + 1) columns; a perfect hash family PHF(3; k, v, 3) of Shangguan
  and Ge (2016, from 3-AP-free sets) or of Fuji-Hara (2015, from quadrics and Hermitian varieties) composed with the
  covering array CA(2q^3 - 1; 3, q^2 + q + 1, q) of Raaphorst, Moura and Stevens, 6q^3 - 5 rows; and the oversampling
  existence bound for a CPHF with n - 1 rows (Colbourn, Lanus and Sarkar, Des. Codes Cryptogr. 2018, as restated by
  Colbourn, 2024);
- (b*) the same oversampling method applied to a Sherwood CPHF with one, two or three restricted pairs of rows
  (Colbourn and Lanus, 2018): q^2 - q fewer rows than ours for each restricted pair;
- (t) the oversampling method for a Sherwood CPHF with our n rows: the same size as ours (a tie);
- (a) none of these reaches k: our array is smaller than every published construction we found.

Two programs, written separately, compute these ranges and agree on every family; a fresh clone reproduces their
outputs (they are not yet in this repository). Not read in full, and so open: Dougherty's tables of perfect hash
families, the 2018 papers of Colbourn, Lanus and Sarkar and of Colbourn and Lanus, and Shokri and Moura's paper itself.

| folder | rows n | past-table widths | (b) explicit construction smaller | (b*) restricted oversampling smaller | (t) tie with oversampling | (a) smaller than all found | counted (a) + (t) |
|---|---|---|---|---|---|---|---|
| [CA_1024_3_165004_4](CA_1024_3_165004_4/) | 17 | 65,004 (k 100,001 to 165,004) | none | none | none | 65,004 (k 100,001 to 165,004) | 65,004 |
| [CA_1685_3_154375_5](CA_1685_3_154375_5/) | 14 | 54,375 (k 100,001 to 154,375) | none | none | none | 54,375 (k 100,001 to 154,375) | 54,375 |
| [CA_3703_3_137618_7](CA_3703_3_137618_7/) | 11 | 37,618 (k 100,001 to 137,618) | none | none | none | 37,618 (k 100,001 to 137,618) | 37,618 |
| [CA_5048_3_116455_8](CA_5048_3_116455_8/) | 10 | 16,455 (k 100,001 to 116,455) | none | none | none | 16,455 (k 100,001 to 116,455) | 16,455 |
| [CA_7209_3_221150_9](CA_7209_3_221150_9/) | 10 | 121,150 (k 100,001 to 221,150) | none | none | none | 121,150 (k 100,001 to 221,150) | 121,150 |
| [CA_11891_3_207658_11](CA_11891_3_207658_11/) | 9 | 107,658 (k 100,001 to 207,658) | none | none | none | 107,658 (k 100,001 to 207,658) | 107,658 |
| [CA_17485_3_134368_13](CA_17485_3_134368_13/) | 8 | 34,368 (k 100,001 to 134,368) | none | none | none | 34,368 (k 100,001 to 134,368) | 34,368 |
| [CA_32656_3_322146_16](CA_32656_3_322146_16/) | 8 | 222,146 (k 100,001 to 322,146) | none | none | none | 222,146 (k 100,001 to 322,146) | 222,146 |
| [CA_34289_3_106533_17](CA_34289_3_106533_17/) | 7 | 6,533 (k 100,001 to 106,533) | none | none | none | 6,533 (k 100,001 to 106,533) | 6,533 |
| [CA_47899_3_160839_19](CA_47899_3_160839_19/) | 7 | 60,839 (k 100,001 to 160,839) | none | none | none | 60,839 (k 100,001 to 160,839) | 60,839 |
| [CA_85031_3_302074_23](CA_85031_3_302074_23/) | 7 | 202,074 (k 100,001 to 302,074) | none | none | none | 202,074 (k 100,001 to 302,074) | 202,074 |
| [CA_109225_3_408135_25](CA_109225_3_408135_25/) | 7 | 308,135 (k 100,001 to 408,135) | none | none | none | 308,135 (k 100,001 to 408,135) | 308,135 |
| [CA_117963_3_108143_27](CA_117963_3_108143_27/) | 6 | 87,704 (k 20,440 to 108,143) | 757 (k 20,440 to 21,196) | none | none | 86,947 (k 21,197 to 108,143) | 86,947 |
| [CA_146189_3_135764_29](CA_146189_3_135764_29/) | 6 | 110,505 (k 25,260 to 135,764) | 871 (k 25,260 to 26,130) | none | none | 109,634 (k 26,131 to 135,764) | 109,634 |
| [CA_178591_3_167721_31](CA_178591_3_167721_31/) | 6 | 136,938 (k 30,784 to 167,721) | 993 (k 30,784 to 31,776) | none | none | 135,945 (k 31,777 to 167,721) | 135,945 |
| [CA_196448_3_184913_32](CA_196448_3_184913_32/) | 6 | 151,089 (k 33,825 to 184,913) | none | none | none | 151,089 (k 33,825 to 184,913) | 151,089 |
| [CA_137619_3_534635_27](CA_137619_3_534635_27/) | 7 | 349,722 (k 184,914 to 534,635) | none | none | none | 349,722 (k 184,914 to 534,635) | 349,722 |
| [CA_170549_3_684678_29](CA_170549_3_684678_29/) | 7 | 499,765 (k 184,914 to 684,678) | none | none | none | 499,765 (k 184,914 to 684,678) | 499,765 |
| [CA_208351_3_860049_31](CA_208351_3_860049_31/) | 7 | 675,136 (k 184,914 to 860,049) | none | none | none | 675,136 (k 184,914 to 860,049) | 675,136 |
| [CA_229184_3_944542_32](CA_229184_3_944542_32/) | 7 | 759,629 (k 184,914 to 944,542) | none | none | none | 759,629 (k 184,914 to 944,542) | 759,629 |
| [CA_354349_3_647632_37](CA_354349_3_647632_37/) | 7 | 595,573 (k 52,060 to 647,632) | 108,992 (k 52,060 to 161,051) | 31,486 (k 161,052 to 192,537) | 72,726 (k 192,538 to 265,263) | 382,369 (k 265,264 to 647,632) | 455,095 |
| [CA_482201_3_643825_41](CA_482201_3_643825_41/) | 7 | 573,182 (k 70,644 to 643,825) | 108,549 (k 70,644 to 179,192) | 98,259 (k 179,193 to 277,451) | 105,747 (k 277,452 to 383,198) | 260,627 (k 383,199 to 643,825) | 366,374 |
| [CA_2722681_3_10998546_73](CA_2722681_3_10998546_73/) | 7 | 10,604,127 (k 394,420 to 10,998,546) | 1,025,438 (k 394,420 to 1,419,857) | 722,976 (k 1,419,858 to 2,142,833) | 847,051 (k 2,142,834 to 2,989,884) | 8,008,662 (k 2,989,885 to 10,998,546) | 8,855,713 |
| [CA_6388129_3_13008618_97](CA_6388129_3_13008618_97/) | 7 | 12,086,439 (k 922,180 to 13,008,618) | 2,116,861 (k 922,180 to 3,039,040) | 2,803,475 (k 3,039,041 to 5,842,515) | 2,336,379 (k 5,842,516 to 8,178,894) | 4,829,724 (k 8,178,895 to 13,008,618) | 7,166,103 |
| [CA_9064549_3_15996200_109](CA_9064549_3_15996200_109/) | 7 | 14,689,181 (k 1,307,020 to 15,996,200) | 2,912,405 (k 1,307,020 to 4,219,424) | 4,592,805 (k 4,219,425 to 8,812,229) | 3,537,620 (k 8,812,230 to 12,349,849) | 3,646,351 (k 12,349,850 to 15,996,200) | 7,183,971 |
| [CA_50322241_3_25366664_193](CA_50322241_3_25366664_193/) | 7 | 18,140,165 (k 7,226,500 to 25,366,664) | 18,140,165 (k 7,226,500 to 25,366,664) | none | none | none | 0 |
| [CA_1588501_3_9757994_61](CA_1588501_3_9757994_61/) | 7 | 9,527,231 (k 230,764 to 9,757,994) | 419,225 (k 230,764 to 649,988) | 485,612 (k 649,989 to 1,135,600) | 444,789 (k 1,135,601 to 1,580,389) | 8,177,605 (k 1,580,390 to 9,757,994) | 8,622,394 |
| [CA_2104939_3_9609828_67](CA_2104939_3_9609828_67/) | 7 | 9,304,509 (k 305,320 to 9,609,828) | 743,257 (k 305,320 to 1,048,576) | 533,940 (k 1,048,577 to 1,582,516) | 622,949 (k 1,582,517 to 2,205,465) | 7,404,363 (k 2,205,466 to 9,609,828) | 8,027,312 |
| [CA_9064549_3_33994950_109](CA_9064549_3_33994950_109/) | 7 | 17,998,750 (k 15,996,201 to 33,994,950) | none | none | none | 17,998,750 (k 15,996,201 to 33,994,950) | 17,998,750 |
| [CA_354349_3_1751572_37](CA_354349_3_1751572_37/) | 7 | 1,103,940 (k 647,633 to 1,751,572) | none | none | none | 1,103,940 (k 647,633 to 1,751,572) | 1,103,940 |
| [CA_556291_3_2908356_43](CA_556291_3_2908356_43/) | 7 | 2,826,957 (k 81,400 to 2,908,356) | 130,169 (k 81,400 to 211,568) | 117,074 (k 211,569 to 328,642) | 125,743 (k 328,643 to 454,385) | 2,453,971 (k 454,386 to 2,908,356) | 2,579,714 |
| [CA_6388129_3_27995660_97](CA_6388129_3_27995660_97/) | 7 | 14,987,042 (k 13,008,619 to 27,995,660) | none | none | none | 14,987,042 (k 13,008,619 to 27,995,660) | 14,987,042 |
| [CA_2722681_3_19242664_73](CA_2722681_3_19242664_73/) | 7 | 8,244,118 (k 10,998,547 to 19,242,664) | none | none | none | 8,244,118 (k 10,998,547 to 19,242,664) | 8,244,118 |
| **all** | | **124,688,057** | **25,707,682** | **9,385,627** | **8,093,004** | **81,501,744** | **89,594,748** |

## What each folder holds

- `NAME.cphf.txt`: the family. It uses the coding of the ca-tools certificates: a point (1, x, y) is the integer (1 q + x) q + y, and a field element of GF(p^e) is the integer of its base-p digits modulo the Conway polynomial of ca-tools' tools/cphf/cphfcheck.c. The file has two header lines and n rows of k point ids.
- `NAME.scphf_check.out`: the exact check of every column triple by checker/pq_scphf3_bigcheck.c, on the search output in our own coding.
- `NAME.conway_check.out`: the same checker, on this file, in the Conway field.
- `NAME.fullcheck3.out`: checker/fullcheck3.c, a second exact checker written separately from the search and from pq_scphf3_bigcheck.c, on this file. Its log records the file's SHA-256 before and after the run, and the self-test that runs first.
- `certificates.csv`: the family as a ca-tools certificate. From a ca-tools checkout, `python3 tools/check_certificates.py PATH/wide/NAME` checks it exactly, with that repository's own checker. family_sha256, the hash of its canonical form `cphf1`, is in the notes.

Every family passed all three checks, on the numbers of triples C(k, 3).

## How they were found

Each family was grown column by column by `code/search/pq_cphf3big_v3.c` (MIT), built with
`cc -O3 -march=native -o pq_cphf3big pq_cphf3big_v3.c -lm`. It was run as
`PQ_START=START pq_cphf3big q n 1000000 40000 SEED OUT 3600 3 16`, with these settings:

- at most 1,000,000 columns and 40,000 CPU seconds;
- stop after 3,600 seconds without a new best;
- at most 3 conflicting pairs for a column added after failed tries;
- 16 tries per column;
- SEED 1000 + q;
- START the 100,000-column family of the same q and n. For q up to 25 that is the family of ca-tools pull request #51; for q = 27 to 32 it is our run q27_n6 to q32_n6.

The search can remove columns, so a family does not contain its start unchanged. The searches stopped on the time limit or after 3,600 seconds without a new best, so a rerun with the same seed may stop at another width. The family files are the certificates.

## Still running

- q = 27, 29, 31 and 32 with n = 7: still growing. At 01:30 on 8 November they had 533,316, 676,940, 845,154 and 848,743 columns. Each is added once it has finished and passed all three checks.

The search, the checkers and these files were prepared with the help of Claude, an AI system from Anthropic. Arhan
Canli takes responsibility for them.
