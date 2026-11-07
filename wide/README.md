# Strength 3 past 100,000 columns, and alphabets 27 to 32 (8 November 2026)

Fifteen Sherwood covering perfect hash families of strength 3 are kept here, one folder each. Eleven take the ladders
of q = 5 to 25 past 100,000 columns, up to 408,135. Four are over the alphabets 27, 29, 31 and 32. All of them lie
outside the scope of the ca-tools covering array table, which keeps strengths 2 to 6, alphabets up to 25 and widths
up to 100,000 (Christopher Smolen, ca-tools issue #54, 7 November 2026). So the table does not list them, and we keep
them here.

Each family is an n x k array of points of the affine plane AG(2, q), every vector with first coordinate 1. By the
theorem of Sherwood, Martirosyan and Colbourn (J. Combin. Des. 14 (2006) 202-213) it gives
CA(n(q^3 - q) + q; 3, k, q). By Lemma 3.1 of Colbourn, Keri, Rivas Soriano and Schlage-Puchta (Discrete Appl. Math.
158 (2010) 1158-1180), fusing m symbols then gives CA(n(q^3 - q) + q - 2m; 3, k, q - m) for every smaller alphabet.

## The families and the cells they fill

A cell is a strength, alphabet and width (3, v, k). Below, a cell is counted when all three of these hold:

- the ca-tools table has no entry for it today (k above 100,000 at v up to 25; any k above 25);
- the family, or its fused array, gives an array there;
- the constructions of the ca-tools derived lookup give no smaller size there. We ran tools/derive_table.py from ca-tools at commit ce719cb on a copy of the table, with these families and their fused arrays added and its ladder of widths continued past 100,000.

That lookup has no baseline above 25. So for v above 25 we also left out k up to q(q^2 + q + 1). There, the construction of Shokri and Moura (J. Combin. Des. 2025), with Bush's orthogonal array CA(q^3; 3, q + 1, q) as its ingredient, gives about 3% fewer rows than these arrays. Here q is the alphabet, or the next prime power above it.

In all, 4,338,171 cells: 1,657,587 at the families' own alphabets and 2,680,584 by fusing. Smaller arrays may still be known for some of these cells from constructions that the lookup does not cover.

| folder | family | array | cells at v = q | cells by fusing |
|---|---|---|---|---|
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

- q = 4, n = 17: the search stopped at 165,004 columns on 8 November 2026. Its folder is added when all three checks pass.
- q = 27, 29, 31 and 32 with n = 7: still growing. At 01:30 on 8 November they had 533,316, 676,940, 845,154 and 848,743 columns. Each is added once it has finished and passed all three checks.

The search, the checkers and these files were prepared with the help of Claude, an AI system from Anthropic. Arhan
Canli takes responsibility for them.
