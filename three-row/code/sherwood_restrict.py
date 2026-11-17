#!/usr/bin/env python3
"""sherwood_restrict.py IN OUT -- the Sherwood restriction of the q = 16 family (Corollary in the README).
IN: families/CA_12286_3_546_16.cphf.txt (3 lines of 546 integers, GF(16)^3 vectors in base 16, Conway coding).
Keeps the columns whose rows 1 and 3 are off the line L: X0 = 0 and whose row 2 is off the line l: X0 + 4 X1 + 3 X2 = 0
(dual coordinates; this pair keeps the most columns, 468, over all choices of one line per row). Then each row is
written in affine coordinates: rows 1 and 3 by the vector itself, row 2 after the map (X0, X1, X2) -> (X0 + 4X1 + 3X2, X1, X2),
and every vector scaled so that its first coordinate is 1. OUT: 3 lines of 468 integers; it gives a Sherwood
CPHF(3; 468, 16, 3), hence CA(3(16^3 - 16) + 16; 3, 468, 16) = CA(12256; 3, 468, 16)."""
import sys
Q, POLY = 16, 0x13
def mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a & Q: a ^= POLY
    return r
def inv(a):
    return next(x for x in range(1, Q) if mul(a, x) == 1)
def vec(n): return [n // 256, (n // 16) % 16, n % 16]
rows = [[vec(int(t)) for t in line.split()] for line in open(sys.argv[1]) if line.strip()]
k = len(rows[0])
def f2(v): return v[0] ^ mul(4, v[1]) ^ mul(3, v[2])
keep = [c for c in range(k) if rows[0][c][0] and rows[2][c][0] and f2(rows[1][c])]
out = []
for r in range(3):
    line = []
    for c in keep:
        v = rows[r][c]
        if r == 1: v = [f2(v), v[1], v[2]]
        s = inv(v[0]); v = [mul(s, x) for x in v]
        assert v[0] == 1
        line.append(256 + 16 * v[1] + v[2])
    out.append(" ".join(map(str, line)))
open(sys.argv[2], "w").write("\n".join(out) + "\n")
print("kept %d columns" % len(keep))
