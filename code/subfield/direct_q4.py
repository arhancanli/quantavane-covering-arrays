"""Direct check, in GF(4^5) = GF(2^10), of the universal sets for q = 4, d = 5 (x = 11) found by usearch.

For a set J of 6 columns: J is uncovered by the row a^j iff the 5 differences a^{j_i} - a^{j_0} are F_4-dependent,
iff the 10 vectors w*u_i (w in {1, omega}, omega a generator of F_4^*) have F_2-rank < 10.
"""
import random, subprocess, sys

DEG = 10
# find an irreducible (primitive) polynomial of degree 10 over F_2
def mul(a, b, mod):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> DEG:
            a ^= mod
    return r

def order_of_x(mod):
    v = 1
    for k in range(1, 2 ** DEG):
        v = mul(v, 2, mod)
        if v == 1:
            return k
    return None

MOD = None
for c in range(1, 2 ** DEG, 2):
    mod = (1 << DEG) | c
    if order_of_x(mod) == 2 ** DEG - 1:
        MOD = mod
        break
N = 2 ** DEG - 1
pw = [1]
for _ in range(N - 1):
    pw.append(mul(pw[-1], 2, MOD))
omega = pw[N // 3]  # generator of F_4^*

def rank2(vecs):
    basis = {}
    rk = 0
    for v in vecs:
        while v:
            h = v.bit_length() - 1
            if h in basis:
                v ^= basis[h]
            else:
                basis[h] = v
                rk += 1
                break
    return rk

def uncovered(a_exp, J):
    pts = [pw[(a_exp * j) % N] for j in J]
    u = [p ^ pts[0] for p in pts[1:]]
    vecs = u + [mul(x, omega, MOD) for x in u]
    return rank2(vecs) < 10

def universal(J):
    return all(uncovered(e, J) for e in range(N))

found = []
out = subprocess.run(['./usearch', '2', '1', '5', '2', '30'], capture_output=True, text=True).stdout
for line in out.split():
    if line.startswith('M='):
        found.append([int(v) for v in line[2:].split(',')])
print('usearch sets:', len(found))
bad = [M for M in found if not universal([11 * m for m in M])]
print('universal by direct check:', len(found) - len(bad), 'of', len(found))
random.seed(1)
foundset = {tuple(M) for M in found}
nonu = 0
tried = 0
while tried < 300:
    M = [0] + sorted(random.sample(range(1, 31), 5))
    if tuple(M) in foundset:
        continue
    tried += 1
    if not universal([11 * m for m in M]):
        nonu += 1
print('random non-listed sets that some row covers:', nonu, 'of', tried)
# exhaustive: every 6-set in 11Z with max <= 30*11, universal by direct check iff listed
allc = 0
mism = 0
import itertools
for rest in itertools.combinations(range(1, 31), 5):
    M = (0,) + rest
    allc += 1
    u = universal([11 * m for m in M])
    if u != (M in foundset):
        mism += 1
print('exhaustive direct check over', allc, 'sets: mismatches', mism)
