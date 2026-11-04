"""Exact check of a CPHF file in the ca-tools format (n lines of k base-q integers, Conway coding), our own code:
for every (t-1)-prefix of columns and every row, the hyperplane through the prefix vectors (when independent) and the
dot product of its normal with every later column; every t-set must be covered in some row.
  python3 -I independent/cphf_conway_check.py FILE t q   (1 Nov 2026: 0 uncovered on CA_26217_4_87_9 and
  CA_16360_4_74_8 as converted; 354 uncovered when q 9 is converted without the field isomorphism)"""
import itertools
import math
import sys

import numpy as np

CONWAY = {4: (2, [1, 1]), 8: (2, [1, 1, 0]), 16: (2, [1, 1, 0, 0]), 32: (2, [1, 0, 1, 0, 0]),
          9: (3, [2, 2]), 27: (3, [1, 2, 0]), 25: (5, [2, 4])}


def tables(q):
    if q not in CONWAY:
        a = np.arange(q)
        return (a[:, None] + a[None, :]) % q, (a[:, None] * a[None, :]) % q
    p, f = CONWAY[q]
    e = len(f)
    dig = lambda x: [(x // p ** i) % p for i in range(e)]
    add = np.zeros((q, q), dtype=np.int64)
    mul = np.zeros((q, q), dtype=np.int64)
    for a in range(q):
        for b in range(q):
            add[a, b] = sum(((x + y) % p) * p ** i for i, (x, y) in enumerate(zip(dig(a), dig(b))))
            prod = [0] * (2 * e)
            for i, x in enumerate(dig(a)):
                for j, y in enumerate(dig(b)):
                    prod[i + j] = (prod[i + j] + x * y) % p
            for d in range(2 * e - 2, e - 1, -1):
                c, prod[d] = prod[d], 0
                for i in range(e):
                    prod[d - e + i] = (prod[d - e + i] - c * f[i]) % p
            mul[a, b] = sum(c * p ** i for i, c in enumerate(prod[:e]))
    return add, mul


def main():
    path, t, q = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    add, mul = tables(q)
    inv = np.zeros(q, dtype=np.int64)
    for a in range(1, q):
        inv[a] = int(np.nonzero(mul[a] == 1)[0][0])
    neg = np.array([int(np.nonzero(add[a] == 0)[0][0]) for a in range(q)])
    rows = [list(map(int, l.split())) for l in open(path) if l.strip() and not l.startswith('#')]
    k = len(rows[0])
    V = [np.array([[(x // q ** (t - 1 - j)) % q for j in range(t)] for x in row], dtype=np.int64) for row in rows]
    assert all((v[:, 0] == 1).all() for v in V), "not affine"

    def normal(M):
        """A nonzero w with w . m = 0 for every row m of M ((t-1) x t), or None when the rows are dependent."""
        M = [list(r) for r in M]
        piv, r = [], 0
        for col in range(t):
            pr = next((i for i in range(r, len(M)) if M[i][col]), None)
            if pr is None:
                continue
            M[r], M[pr] = M[pr], M[r]
            s = inv[M[r][col]]
            M[r] = [int(mul[s, x]) for x in M[r]]
            for i in range(len(M)):
                if i != r and M[i][col]:
                    c = neg[M[i][col]]
                    M[i] = [int(add[x, mul[c, y]]) for x, y in zip(M[i], M[r])]
            piv.append(col)
            r += 1
        if r < t - 1:
            return None
        free = next(c for c in range(t) if c not in piv)
        w = [0] * t
        w[free] = 1
        for i, pc in enumerate(piv):          # pivot var = -M[i][free]
            w[pc] = int(neg[M[i][free]])
        return w

    bad = 0
    for pre in itertools.combinations(range(k), t - 1):
        last = pre[-1]
        if last == k - 1:
            continue
        cov = np.zeros(k - last - 1, dtype=bool)
        for v in V:
            w = normal([v[c] for c in pre])
            if w is None:
                continue
            acc = np.zeros(k - last - 1, dtype=np.int64)
            for i in range(t):
                acc = add[acc, mul[w[i], v[last + 1:, i]]]
            cov |= acc != 0
            if cov.all():
                break
        bad += int((~cov).sum())
    print(f"{path}: {math.comb(k, t)} {t}-sets, {bad} uncovered")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
