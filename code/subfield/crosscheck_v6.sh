#!/bin/sh
# Cross-checks of the three implementations of the criterion of Theorem 4.3(b): usearch (C, enumerates every
# candidate), usearch2 (C, solves for one element) and explore.py (Python, separate code: ranks over F_p of the
# F_p-span of omega^k beta^m). For each case the sorted lists of sets M must be identical.
# Version 6: the one case of Table 1 that crosscheck.sh (log logs/crosscheck.log) did not
# include, d = 3 and q = 16 with r = 2 (p f d g W = 2 1 3 4 6).
# Run from this directory: sh crosscheck_v6.sh > logs/crosscheck_v6.log 2>&1
set -e
cc -O2 -o usearch usearch.c
cc -O2 -o usearch2 usearch2.c
T=${TMPDIR:-/tmp}/qv_crosscheck.$$
mkdir -p $T
for a in "2 1 3 4 6"; do
  set -- $a
  ./usearch $a 2>/dev/null | sed -n 's/^M=\([^ ]*\).*/\1/p' | sort > $T/u1
  ./usearch2 $a 2>/dev/null | sed -n 's/^M=\([^ ]*\).*/\1/p' | sort > $T/u2
  python3 -I explore.py $a | sed -n 's/^(\([0-9, ]*\)).*/\1/p' | tr -d ' ' | sort > $T/u3
  n1=$(wc -l < $T/u1 | tr -d ' '); n2=$(wc -l < $T/u2 | tr -d ' '); n3=$(wc -l < $T/u3 | tr -d ' ')
  if cmp -s $T/u1 $T/u2 && cmp -s $T/u1 $T/u3; then v=IDENTICAL; else v=DIFFERENT; fi
  echo "p f d g W = $a: usearch $n1, usearch2 $n2, explore.py $n3 sets: $v"
done
rm -rf $T
