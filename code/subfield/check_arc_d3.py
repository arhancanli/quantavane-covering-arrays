"""Check of Theorem 4.8(a) (d = 3): for every 3-set S in [0, D_1(r)), the elements theta^s or theta^(-s) (s in S)
span GF(r^3) over F_r (equivalently: the points are not collinear in PG(2, r) for theta or for theta^-1).
    python3 -I check_arc_d3.py
Uses the field code of explore.py (prime r only)."""
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from explore import Field, rank_mod_p
for r in (2, 3, 5, 7):
    K = Field(r, 3)
    N = r ** 3 - 1
    D1 = (r ** 3 - 1) // (r - 1)
    bad = 0
    total = 0
    for S in itertools.combinations(range(D1), 3):
        total += 1
        r1 = rank_mod_p([K.powvec(s) for s in S], r)
        r2 = rank_mod_p([K.powvec(-s % N) for s in S], r)
        if r1 < 3 and r2 < 3:
            bad += 1
    print(f"r = {r}: {total} sets of three points, collinear for both theta and theta^-1: {bad}")
