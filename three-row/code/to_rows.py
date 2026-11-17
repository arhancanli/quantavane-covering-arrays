#!/usr/bin/env python3
"""to_rows.py IN OUT -- turn kummer_dump's output (one column per line, three vectors "a0,a1,a2") into the ca-tools
certificate layout: three lines of k integers, each vector written in base 16, most significant digit first
(a0*256 + a1*16 + a2). GF(16) elements are already in the Conway coding (x^4 + x + 1, codes c0 + 2c1 + 4c2 + 8c3)."""
import sys
cols = [[tuple(int(c) for c in e.split(",")) for e in l.split()] for l in open(sys.argv[1]) if l.strip()]
with open(sys.argv[2], "w") as f:
    for r in range(3):
        f.write(" ".join(str(v[r][0] * 256 + v[r][1] * 16 + v[r][2]) for v in cols) + "\n")
