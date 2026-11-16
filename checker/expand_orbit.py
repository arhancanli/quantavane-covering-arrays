"""Expand a compact orbit family (pq_cphf3orb output) into the explicit array, for tests with the old checkers.
Written apart from the search and the two orbit checkers: it uses only the matrices G1, G2 of the header.
Usage: python3 -I expand_orbit.py q FILE OUT [cert]   (cert: write ids q^2 + x q + y, the ca-tools coding)"""
import sys

q = int(sys.argv[1]); src = sys.argv[2]; dst = sys.argv[3]; cert = len(sys.argv) > 4 and sys.argv[4] == "cert"
M1 = M2 = None; G = {1: {}, 2: {}}; rows = []; first = None
for line in open(src):
    if line.startswith("best"):
        first = line.strip(); continue
    if line.startswith("# orbit family"):
        t = line.split(); M1 = int(t[t.index("M1") + 1]); M2 = int(t[t.index("M2") + 1]); continue
    if line.startswith("# G"):
        t = line.split(); g = int(t[1][1]); r = int(t[2]); G[g][r] = tuple(int(v) % q for v in t[3:7]); continue
    if line[:1].isdigit():
        rows.append([int(v) for v in line.split()])
n = len(rows); R = len(rows[0])
assert M1 and M2 and len(G[1]) == n and len(G[2]) == n

def app(m, pt):
    x, y = divmod(pt, q); a, b, c, d = m
    return ((a * x + b * y) % q) * q + (c * x + d * y) % q

out = []
for r in range(n):
    row = []
    for c in rows[r]:
        v = c
        for i in range(M1):
            w = v
            for j in range(M2):
                row.append(w); w = app(G[2][r], w)
            assert w == v, "G2 does not have order dividing M2"
            v = app(G[1][r], v)
        assert v == c, "G1 does not have order dividing M1"
    out.append(row)
k = R * M1 * M2
with open(dst, "w") as f:
    f.write(f"best k {k} (expanded from {src.split('/')[-1]}: {first})\n" if not cert else f"# expanded from {src.split('/')[-1]}, k {k}\n")
    for row in out:
        f.write(" ".join(str(v + q * q if cert else v) for v in row) + "\n")
print(k)
