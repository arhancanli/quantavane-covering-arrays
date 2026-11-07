"""Randomized test of Theorem 4.3(a) for odd characteristic: for random sets M and random a in GF(q^d)^*, the criterion
(dim R(beta, M) >= 2, or R = F_r rho with sum rho_m c^-m = 0, where a^w = c beta) must agree with a direct test of
affine dependence over F_q of the points a^(w m) in GF(q^d).

    python3 -I test_criterion_a.py

Cases (r prime, q = r^2, d = 3): r = 3 (GF(3^6)) and r = 5 (GF(5^6)); M random with 0 in M and max M <= 120 (so wM
reaches beyond D_1(q)), 4,000 pairs (M, a) per case. Everything here is computed in L = GF(r^(2d)) itself:
F_q = {z : z^q = z}, K = {z : z^(r^d) = z}, and c is found by trying every c in F_q^* with a^w / c in K.
"""
import random
import sys


def find_primitive_poly(p, n):
    N = p ** n - 1
    for code in range(p ** n):
        coeffs = []
        c = code
        for _ in range(n):
            coeffs.append(c % p)
            c //= p
        if coeffs[0] == 0:
            continue
        poly = coeffs + [1]
        v = [1] + [0] * (n - 1)
        pw = [tuple(v)]
        order = None
        for k in range(1, N + 1):
            top = v[-1]
            w = [0] + v[:-1]
            if top:
                w = [(w[i] - top * poly[i]) % p for i in range(n)]
            v = w
            if v == [1] + [0] * (n - 1):
                order = k
                break
            pw.append(tuple(v))
        if order == N:
            return pw
    raise ValueError


def rank_mod_p(rows, p):
    rows = [list(r) for r in rows]
    rank = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(rank, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][c], p - 2, p)
        rows[rank] = [(x * inv) % p for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def nullspace_mod_p(vectors, p):
    """basis of {rho : sum rho_i vectors[i] = 0} over F_p"""
    m = len(vectors)
    n = len(vectors[0])
    # matrix with columns = vectors: solve A rho = 0, A is n x m
    A = [[vectors[j][i] for j in range(m)] for i in range(n)]
    piv_cols = []
    rank = 0
    for c in range(m):
        piv = next((i for i in range(rank, n) if A[i][c] % p), None)
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        inv = pow(A[rank][c], p - 2, p)
        A[rank] = [(x * inv) % p for x in A[rank]]
        for i in range(n):
            if i != rank and A[i][c] % p:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[rank])]
        piv_cols.append(c)
        rank += 1
    free = [c for c in range(m) if c not in piv_cols]
    basis = []
    for fc in free:
        rho = [0] * m
        rho[fc] = 1
        for i, pc in enumerate(piv_cols):
            rho[pc] = (-A[i][fc]) % p
        basis.append(rho)
    return basis


def run(r, d, trials, seed):
    p, g = r, 2
    n = g * d                      # L = GF(p^n)
    pw = find_primitive_poly(p, n)
    N = p ** n - 1
    q = r ** g
    D1 = lambda s: (s ** d - 1) // (s - 1)  # noqa: E731
    w = D1(q) // D1(r)
    log = {v: i for i, v in enumerate(pw)}
    vec = lambda e: pw[e % N]  # noqa: E731
    Fq = [e for e in range(N) if (e * q) % N == e % N]            # exponents of F_q^* elements: e*(q-1) = 0 mod N
    Fq = [e for e in range(N) if (e * (q - 1)) % N == 0]
    Kexp = lambda e: (e * (r ** d - 1)) % N == 0                  # theta^e in K
    omega_e = Fq[1]                                                # a nontrivial element of F_q^* (generates F_q over F_p
    # for q = p^2 any element of F_q \ F_p does); pick one not in F_p
    Fp = [e for e in range(N) if (e * (p - 1)) % N == 0]
    omega_e = next(e for e in Fq if e not in Fp)
    rng = random.Random(seed)
    agree = disagree = uncovered = 0
    for _ in range(trials):
        M = [0] + sorted(rng.sample(range(1, 121), d))
        ae = rng.randrange(N)                                      # a = theta^ae
        he = (ae * w) % N                                          # h = a^w
        # direct: affine dependence over F_q of the points h^m
        pts = [vec(he * m) for m in M]
        diffs = [[(x - y) % p for x, y in zip(P, pts[0])] for P in pts[1:]]
        # F_q-dependence of diffs <=> F_p-rank of {u, omega u} < g*d
        def mul_vec(e1, v):
            if not any(v):
                return [0] * n
            return list(vec(e1 + log[tuple(v)]))
        rows = diffs + [mul_vec(omega_e, u) for u in diffs]
        direct = rank_mod_p(rows, p) < g * d
        # criterion: h = c beta with c in F_q^*, beta in K^*
        ce = next(e for e in Fq if Kexp((he - e) % N))
        be = (he - ce) % N
        R = nullspace_mod_p([list(vec(be * m)) for m in M], p)    # F_p = F_r relations among beta^m
        if len(R) >= 2:
            crit = True
        else:
            rho = R[0]
            # sum rho_m c^-m in F_q: compute as an element of L
            acc = [0] * n
            for rm, m in zip(rho, M):
                if rm:
                    v = vec((-ce * m) % N)
                    acc = [(x + rm * y) % p for x, y in zip(acc, v)]
            crit = not any(acc)
        if crit == direct:
            agree += 1
        else:
            disagree += 1
        uncovered += direct
    print(f"r = {r}, q = {q}, d = {d}, w = {w}: {trials} random (M, a): agree {agree}, disagree {disagree} "
          f"(uncovered in {uncovered})")
    return disagree


if __name__ == "__main__":
    bad = run(3, 3, 4000, 1) + run(5, 3, 4000, 2)
    sys.exit(1 if bad else 0)
