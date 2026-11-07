"""Explore universal subfield obstructions.

Setting: q = r^g, gcd(g, d) = 1, K = GF(r^d), r = p^f.  A (d+1)-set M of multipliers (0 in M) gives the column set
xM, x = D1(q)/D1(r).  Criterion (to be proved): xM is uncovered by every row a^j of GF(q^d) iff for every beta in K^*,
  rank_Fr {beta^m : m in M} <= d-1   or   rank_Fr {beta^m (+) e_{m mod (q-1)} : m in M} <= d.
"""
import itertools, sys
from math import gcd


def conway_like(p, n):
    """find a primitive polynomial of degree n over F_p (coeff list low->high, monic)"""
    N = p ** n - 1
    # factor N
    fac = []
    t = N
    d = 2
    while d * d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0:
                t //= d
        d += 1
    if t > 1:
        fac.append(t)
    for code in range(p ** n):
        coeffs = []
        c = code
        for _ in range(n):
            coeffs.append(c % p)
            c //= p
        if coeffs[0] == 0:
            continue
        poly = coeffs + [1]
        # build x^k mod poly table and test order of x
        def mulx(v):
            # v: list length n, multiply by x mod poly
            top = v[-1]
            w = [0] + v[:-1]
            if top:
                w = [(w[i] - top * poly[i]) % p for i in range(n)]
            return w
        v = [1] + [0] * (n - 1)
        seen_one = None
        pw = [v]
        for k in range(1, N + 1):
            v = mulx(v)
            pw.append(v)
            if v == [1] + [0] * (n - 1):
                seen_one = k
                break
        if seen_one == N:
            return poly, pw[:N]
    raise ValueError


class Field:
    def __init__(self, p, n):
        self.p, self.n = p, n
        self.poly, pw = conway_like(p, n)
        self.N = p ** n - 1
        self.vec = [tuple(v) for v in pw]  # theta^i as F_p vector

    def powvec(self, i):
        return self.vec[i % self.N]


def rank_mod_p(rows, p):
    rows = [list(r) for r in rows]
    rank = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = None
        for i in range(rank, len(rows)):
            if rows[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][c], p - 2, p)
        rows[rank] = [(x * inv) % p for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def setup(p, f, d, g):
    r = p ** f
    q = r ** g
    K = Field(p, f * d)
    D1r = (r ** d - 1) // (r - 1)
    D1q = (q ** d - 1) // (q - 1)
    x = D1q // D1r
    assert x * D1r == D1q
    # omega: primitive element of F_r inside K: theta^D1r
    # F_p basis of F_r: omega^0..omega^(f-1) (omega generates F_r over F_p)
    # beta representatives: theta^b, b in [0, D1r), up to Frobenius b -> r b mod D1r
    reps = []
    seen = set()
    for b in range(D1r):
        if b in seen:
            continue
        orb = set()
        c = b
        while c not in orb:
            orb.add(c)
            c = (c * r) % D1r
        seen |= orb
        reps.append(b)
    return dict(p=p, f=f, d=d, g=g, r=r, q=q, K=K, D1r=D1r, D1q=D1q, x=x, reps=reps)


def universal(S, M, return_fail=False):
    p, f, d, r, q, K = S['p'], S['f'], S['d'], S['r'], S['q'], S['K']
    D1r = S['D1r']
    classes = sorted(set(m % (q - 1) for m in M))
    cidx = {c: i for i, c in enumerate(classes)}
    s = len(classes)
    for b in S['reps']:
        # vectors omega^k beta^m over F_p, omega = theta^D1r
        rows = []
        ext = []
        for m in M:
            for k in range(f):
                e = b * m + k * D1r
                v = list(K.powvec(e))
                rows.append(v)
                tail = [0] * (s * f)
                tail[cidx[m % (q - 1)] * f + k] = 1
                ext.append(v + tail)
        rk = rank_mod_p(rows, p) // f
        if rk <= d - 1:
            continue
        rk2 = rank_mod_p(ext, p) // f
        if rk2 <= d:
            continue
        return (False, b) if return_fail else False
    return (True, None) if return_fail else True


def search(p, f, d, g, W=None, limit=None):
    S = setup(p, f, d, g)
    if W is None:
        W = S['D1r'] - 1
    found = []
    for rest in itertools.combinations(range(1, W + 1), d):
        M = (0,) + rest
        if universal(S, M):
            found.append(M)
            if limit and len(found) >= limit:
                break
    return S, found


if __name__ == '__main__':
    p, f, d, g = map(int, sys.argv[1:5])
    W = int(sys.argv[5]) if len(sys.argv) > 5 else None
    S, found = search(p, f, d, g, W)
    print(f"r={S['r']} q={S['q']} d={d} x={S['x']} D1r={S['D1r']} D1q={S['D1q']} W={W or S['D1r']-1} "
          f"reps={len(S['reps'])} found={len(found)}")
    for M in found[:60]:
        cls = [m % (S['q'] - 1) for m in M]
        print(M, 'max*x=', max(M) * S['x'], 'classes', cls, 'beta-exp', [m % (S['r'] ** d - 1) for m in M])
