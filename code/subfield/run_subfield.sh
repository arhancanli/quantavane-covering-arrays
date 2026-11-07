#!/bin/sh
# Computations behind Theorem 4.5 of the paper (subfield obstructions; exact widths of
# all-multiplicative families). Run from this directory: sh run_subfield.sh [quick|all]
#   usearch p f d g W   lists the sets M (0 in M, max M <= W, |M| = d+1) for which the column set wM is
#                       uncovered by every multiplicative row of GF(q^d), q = r^g, r = p^f, by the criterion of
#                       Theorem 4.3(b) (F_r-linear algebra in K = GF(r^d) only).
#   allrows2 e d W      lists every (d+1)-set J with 0 in J and max J <= W that is uncovered by EVERY row a^j of
#                       GF(q^d), q = 2^e (direct computation in GF(q^d), one row per class {a^(2^i)}).
#   direct_q4.py        checks Theorem 4.3(b) against direct computation in GF(4^5) for all 142,506 sets in 11Z
#                       with max <= 330.
#   explore.py          a second, separate implementation of the criterion (Python), used to cross-check usearch.
# Logs go to $LOGDIR (default ./logs). The full runs for (q, r) = (9, 3), (16, 4) and (25, 5) take hours on a shared machine.
set -e
L=${LOGDIR:-logs}; mkdir -p $L
cc -O2 -o usearch usearch.c
cc -O2 -o allrows2 allrows2.c
run() { echo "\$ $*" ; "$@" ; }
{
  echo "# strength 6 (d = 5)"
  run ./usearch 2 1 5 2 30      # q = 4,  r = 2: w = 11
  run ./usearch 2 1 5 3 30      # q = 8,  r = 2: w = 151
  run ./usearch 2 1 5 4 30      # q = 16, r = 2: w = 2255
  run ./usearch 2 1 5 6 30      # q = 64, r = 2 (all classes distinct)
  run ./usearch 5 1 5 2 19      # q = 25, r = 5: widths below 10,000
  run ./usearch 2 2 5 2 48      # q = 16, r = 4: widths below 10,000
  echo "# strength 5 (d = 4)"
  run ./usearch 2 1 4 3 14      # q = 8, r = 2: w = 39
  echo "# strength 4 (d = 3)"
  run ./usearch 2 1 3 2 6       # q = 4
  run ./usearch 3 1 3 2 12      # q = 9
  run ./usearch 2 1 3 4 6       # q = 16, r = 2
  run ./usearch 2 2 3 2 20      # q = 16, r = 4
  run ./usearch 5 1 3 2 30      # q = 25
  echo "# cross-check of the F_4 arithmetic on a case with known sets (q = 64, d = 4, r = 4)"
  run ./usearch 2 2 4 3 34
  run python3 -I explore.py 2 2 4 3 34
} > $L/subfield_quick.log 2>&1
{
  run ./allrows2 2 5 132        # q = 4, strength 6: all 6-sets within 133 columns
  run ./allrows2 3 4 200        # q = 8, strength 5
  run ./allrows2 2 4 40         # q = 4, strength 5
} > $L/allrows.log 2>&1
python3 -I direct_q4.py > $L/direct_q4.log 2>&1
if [ "$1" = all ]; then
  cc -O2 -o usearch2 usearch2.c
  run ./usearch2 3 1 5 2 120 > $L/subfield_q9_full.log 2>&1        # q = 9: all 1.9e8 candidates (seconds)
  run ./usearch2 2 2 5 2 340 > $L/subfield_q16r4_full.log 2>&1     # q = 16, r = 4: all 3.7e10 candidates (minutes)
  for s in 0 1 2; do                                               # q = 25: all 2.4e12 candidates (hours), 3 slices
    run ./usearch2 5 1 5 2 780 5 $s 3 > $L/subfield_q25_full_s$s.log 2>&1 &
  done; wait
  # Conjecture 4.6 for small (r, d): q - 1 > W, so all classes are distinct; PRIM=1 keeps primitive classes only
  for a in "2 1 5 7 30" "3 1 5 7 120" "2 1 3 7 6" "3 1 3 7 12" "2 2 3 7 20" "5 1 3 7 30"; do
    echo "\$ PRIM=1 ./usearch2 $a"; PRIM=1 ./usearch2 $a 2>&1 | grep -v "^done"
  done > $L/conjecture_rank.log 2>&1
fi
