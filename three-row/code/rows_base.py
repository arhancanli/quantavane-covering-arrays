#!/usr/bin/env python3
"""rows_base.py IN q OUT -- one-column-per-line vectors "a0,a1,a2" (prime q) -> the ca-tools layout: 3 lines of k
integers a0*q^2 + a1*q + a2 (base q, most significant digit first)."""
import sys
q = int(sys.argv[2])
cols = [[tuple(int(c) for c in e.split(",")) for e in l.split()] for l in open(sys.argv[1]) if l.strip()]
with open(sys.argv[3], "w") as f:
    for r in range(len(cols[0])):
        f.write(" ".join(str(v[r][0] * q * q + v[r][1] * q + v[r][2]) for v in cols) + "\n")
