"""Checks with conventional software: the finite-field arithmetic and linear algebra of the galois library
(M. Hostetter, https://github.com/mhostetter/galois, written by people, not by an AI system), version 0.4.11, on
numpy 2.0.2. This driver script was written with AI help (Claude); every field operation it performs is a galois
operation.

    python galois_checks.py DATA_REPO q4_sets.txt q8_sets.txt     (python of a virtual environment with galois)

DATA_REPO is the data repository (families.csv, families/); q4_sets.txt and q8_sets.txt are the sets M of Theorem 3.8
for q = 4 and q = 8 as printed by subfield/usearch2 ("M=0,a,b,c,d,e" lines). It prints its log to standard output
(the paper's run: galois_checks.log).

Part A (families). Points of AG(t-1, q) are read from the family files (point id ((x_1 q + x_2) q + ...) q + x_{t-1},
field elements as base-p digit vectors modulo the polynomials of the repository's checkers, which galois is given as
its irreducible polynomials). A set of t columns is covered in a row when the (t-1) x (t-1) matrix of differences
P_j - P_1 has nonzero determinant over GF(q) (galois arithmetic, Leibniz expansion). Checked: every t-set of four
small families of strengths 3 and 4; 300,000 random 5-sets of (t, q, k) = (5, 16, 273) and (5, 23, 10000), and
100,000 random 5-sets of each other strength-5 family with at least 3,000 columns (the ten strength-5 families with
at least 3,000 columns are those with progression rows); 100,000 random base sets (sets containing column 0; by shift
invariance these decide a family whose rows are all progression rows) of every strength-6 family and of the q = 8
prefix family SCPHF(23; 3171, 8, 6), and all 15,504 base sets in 151Z of the latter.
Part B (obstructions). In GF(4^5) = GF(2^10) and GF(8^5) = GF(2^15), built by galois, for one a from every class
{a, a^2, a^4, ...} of nonzero elements: the points a^(w m) and their F_q-affine dependence through the F_2-rank
(galois np.linalg.matrix_rank over GF(2)) of the vectors w_i (P_j - P_0), w_i an F_2-basis of F_q. Checked: the 53
base sets of Theorem 3.8 for q = 4 and the seven for q = 8 are uncovered by every row; 300 random other sets 11M
(q = 4, max M <= 30) are covered by some row.
"""
import itertools
import math
import os
import random
import sys
import time

import numpy as np
import galois

DATA = sys.argv[1]
POLY = {4: (2, [1, 1, 1]), 8: (2, [1, 0, 1, 1]), 16: (2, [1, 0, 0, 1, 1]), 9: (3, [1, 0, 1]), 25: (5, [1, 1, 2])}
_fields = {}


def field(q):
    if q not in _fields:
        if q in POLY:
            p, coeffs = POLY[q]
            _fields[q] = galois.GF(q, irreducible_poly=galois.Poly(coeffs, field=galois.GF(p)))
        else:
            _fields[q] = galois.GF(q)
    return _fields[q]


def read_family(path, q, t):
    rows = [list(map(int, ln.split())) for ln in open(path) if ln[:1].isdigit()]
    F = field(q)
    pts = []
    for r in rows:
        ids = np.array(r, dtype=np.int64)
        coords = []
        for i in range(t - 1):
            coords.append((ids // q ** (t - 2 - i)) % q)
        pts.append(F(np.stack(coords, axis=1)))   # shape (k, t-1)
    return F, pts


PERMS = {}


def det_batch(F, M):
    """determinants of a batch of n x n matrices over F (shape (B, n, n)), by the Leibniz formula"""
    n = M.shape[1]
    if n not in PERMS:
        PERMS[n] = []
        for perm in itertools.permutations(range(n)):
            inv = sum(1 for i in range(n) for j in range(i + 1, n) if perm[i] > perm[j])
            PERMS[n].append((perm, inv % 2))
    total = F.Zeros(M.shape[0])
    for perm, odd in PERMS[n]:
        term = M[:, 0, perm[0]]
        for i in range(1, n):
            term = term * M[:, i, perm[i]]
        total = total - term if odd else total + term
    return total


def covered(F, pts, sets):
    """sets: int array (B, t); returns a bool array: covered by some row"""
    cov = np.zeros(sets.shape[0], dtype=bool)
    for P in pts:
        todo = np.nonzero(~cov)[0]
        if todo.size == 0:
            break
        S = sets[todo]
        base = P[S[:, 0]]                                  # (B, t-1)
        D = P[S[:, 1:]] - base[:, None, :]                 # (B, t-1, t-1)
        dets = det_batch(F, D)
        cov[todo[np.asarray(dets) != 0]] = True
    return cov


def all_tsets(k, t, chunk=400000):
    it = itertools.combinations(range(k), t)
    while True:
        block = list(itertools.islice(it, chunk))
        if not block:
            return
        yield np.array(block, dtype=np.int64)


def part_a(out):
    rng = random.Random(20261107)
    fams = [  # (t, q, n, k, file, mode, sample)
        (3, 7, 4, 234, "CA_1351_3_234_7.cphf.txt", "all", None),
        (3, 16, 3, 338, "CA_12256_3_338_16.cphf.txt", "all", None),
        (4, 7, 4, 62, "CA_9583_4_62_7.cphf.txt", "all", None),
        (4, 8, 4, 74, None, "all", None),
        (5, 16, 6, 273, None, "random", 300000),
        (5, 23, 17, 10000, "CA_109417463_5_10000_23.cphf.txt", "random", 300000),
        (6, 7, 20, 2000, "CA_2352847_6_2000_7.cphf.txt", "base", 100000),
        (6, 9, 18, 2000, "CA_9565785_6_2000_9.cphf.txt", "base", 100000),
        (6, 16, 17, 5000, "CA_285212416_6_5000_16.cphf.txt", "base", 100000),
        (6, 25, 15, 5000, "CA_3662109025_6_5000_25.cphf.txt", "base", 100000),
        (6, 8, 23, 3171, "CA_6029136_6_3171_8.cphf.txt", "base", 100000),
    ]
    import csv
    famcsv = {(int(r["t"]), int(r["q"]), int(r["n"]), int(r["k"])): r["family"]
              for r in csv.DictReader(open(os.path.join(DATA, "families.csv")))}
    # every strength-6 family (random base sets) and every other strength-5 family with at least 3,000 columns
    listed = {(f[0], f[1], f[2], f[3]) for f in fams}
    for (t, q, n, k), name in sorted(famcsv.items()):
        if (t, q, n, k) in listed:
            continue
        if t == 6:
            fams.append((t, q, n, k, os.path.basename(name), "base", 100000))
        elif t == 5 and k >= 3000:
            fams.append((t, q, n, k, os.path.basename(name), "random", 100000))
    for t, q, n, k, name, mode, sample in fams:
        path = os.path.join(DATA, "families", name) if name else os.path.join(DATA, famcsv[(t, q, n, k)])
        if not os.path.exists(path):
            path = os.path.join(DATA, famcsv[(t, q, n, k)])
        F, pts = read_family(path, q, t)
        assert len(pts) == n and pts[0].shape[0] == k, (len(pts), pts[0].shape)
        t0 = time.time()
        tested = unc = 0
        if mode == "all":
            for block in all_tsets(k, t):
                c = covered(F, pts, block)
                tested += block.shape[0]
                unc += int((~c).sum())
            what = f"all {math.comb(k, t):,} sets of {t} columns"
            assert tested == math.comb(k, t)
        elif mode == "random":
            sets = np.array([sorted(rng.sample(range(k), t)) for _ in range(sample)], dtype=np.int64)
            c = covered(F, pts, sets)
            tested, unc = sample, int((~c).sum())
            what = f"{sample:,} random sets of {t} columns"
        else:
            sets = np.array([[0] + sorted(rng.sample(range(1, k), t - 1)) for _ in range(sample)], dtype=np.int64)
            extra = ""
            if q == 8 and k == 3171:
                mult = [list(m) for m in itertools.combinations(range(1, 21), 5)]  # 151 M with max M <= 20 < 3171/151
                special = np.array([[0] + [151 * x for x in m] for m in mult], dtype=np.int64)
                sets = np.concatenate([sets, special])
                extra = f" and all {len(mult):,} base sets in 151Z"
            c = covered(F, pts, sets)
            tested, unc = sets.shape[0], int((~c).sum())
            what = f"{sample:,} random base sets{extra}"
        line = (f"A t={t} q={q} n={n} k={k} ({os.path.basename(path)}): {what}: {tested:,} tested, {unc} uncovered "
                f"[{time.time() - t0:.0f} s]")
        print(line, flush=True)
        out.append(line)


def obstruction_field(e_q, d):
    """L = GF(2^(e_q d)) built by galois (Conway polynomial), F_q = {z : z^q = z}, and an F_2-basis of F_q"""
    L = galois.GF(2 ** (e_q * d))
    q = 2 ** e_q
    g = L.primitive_element
    N = L.order - 1
    w0 = g ** (N // (q - 1))                    # generates F_q^*
    basis = [L(1)] + [w0 ** i for i in range(1, e_q)]
    return L, g, N, basis


def uncovered_by_all(L, g, N, basis, J, e_q, d, classes):
    """True if every row a^j (a over one exponent from each class) leaves the columns J affinely dependent over F_q"""
    GF2 = galois.GF(2)
    for b in classes:
        a = g ** b
        pts = [a ** j for j in J]
        diffs = [pts[i] - pts[0] for i in range(1, len(J))]
        vecs = [(w * u).vector() for u in diffs for w in basis]   # F_2 coordinates (galois)
        M = GF2(np.array([np.asarray(v) for v in vecs]))
        if np.linalg.matrix_rank(M) == e_q * d:
            return False
    return True


def part_b(out, sets4, sets8):
    rng = random.Random(7)
    for e_q, w, sets, label in ((2, 11, sets4, "q = 4"), (3, 151, sets8, "q = 8")):
        d = 5
        L, g, N, basis = obstruction_field(e_q, d)
        # one exponent per class {b, 2b, 4b, ...} modulo N (rows a^j and (a^2)^j cover the same sets)
        seen, classes = set(), []
        for b in range(1, N):
            if b in seen:
                continue
            c = b
            while c not in seen:
                seen.add(c)
                c = (2 * c) % N
            classes.append(b)
        t0 = time.time()
        bad = [M for M in sets if not uncovered_by_all(L, g, N, basis, [w * m for m in M], e_q, d, classes)]
        line = (f"B {label}: {len(sets)} listed sets wM checked over all {len(classes)} row classes of GF(2^{e_q * d}): "
                f"{len(sets) - len(bad)} uncovered by every row, {len(bad)} covered by some row [{time.time() - t0:.0f} s]")
        print(line, flush=True)
        out.append(line)
        if e_q == 2:
            listed = {tuple(M) for M in sets}
            others, tries = 0, 0
            while tries < 300:
                M = tuple([0] + sorted(rng.sample(range(1, 31), 5)))
                if M in listed:
                    continue
                tries += 1
                if not uncovered_by_all(L, g, N, basis, [w * m for m in M], e_q, d, classes):
                    others += 1
            line = f"B q = 4: {tries} random unlisted sets 11M (max M <= 30): {others} covered by some row"
            print(line, flush=True)
            out.append(line)


def main():
    out = [f"galois {galois.__version__}, numpy {np.__version__}"]
    print(out[0])
    sets4 = [tuple(map(int, ln.split()[0][2:].split(","))) for ln in open(sys.argv[2]) if ln.startswith("M=")]
    sets8 = [tuple(map(int, ln.split()[0][2:].split(","))) for ln in open(sys.argv[3]) if ln.startswith("M=")]
    part_b(out, sets4, sets8)
    part_a(out)


if __name__ == "__main__":
    main()
