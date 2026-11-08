"""Version 6: the comparison beyond 10,000 columns (Section 5.4; Section S1 and Table S2 of the supporting information),
recomputed with the strength-3 sizes of Shokri and Moura's theorems among the ingredients and as direct bounds.

    python3 -I wide_v6.py CATOOLS [DATA [OUTDIR]]

CATOOLS  a clone of github.com/chrispbsmolen/ca-tools containing commit ce719cb (read with git show: table/ca_table.csv,
         table/derived.csv, r/livingtable/data/dcan_table.csv)
DATA     the data repository (families.csv), default ~/quantavane-covering-arrays
OUTDIR   where tables/ladder6.tex and tables/v6wide.tex go, default the paper's version-6 folder; the column k/k_O(n)
         is copied from OUTDIR/tables/ladder4.tex when that file exists

This is the yardstick of version 2 (v2/scripts/make_table_v2.py, "The yardstick past 10,000 columns"), copied with its
constructions unchanged: symbol fusion, derivation, composition, Chateauneuf-Kreher doubling, the Roux-type bound
CAN(3,k,v) <= CAN(3,h,v) + (v-1) CAN(2,h,v) + v^3 - v^2 with h = ceil(k/v) (Colbourn, Martirosyan, Tran Van Trung and
Walker 2006, Theorem 3.4), k-ary Roux with Yin's DCAN values, the established part of the power construction, and the
general recursion of Shokri and Moura (thesis Theorem 5.2.6, with CAN(2, q^2+q+1, q) <= 2q^2 - q), each evaluated at
every width 10,001 <= k <= 100,000 with the counted rows of the table at ce719cb and its computed sizes (derived.csv) as
ingredients, repeated until nothing changes.
Run A (as version 2) must reproduce the 11,904 widths at which a construction is smaller than our families.
Run B adds the sizes of Shokri and Moura's Theorems 5.2.7, 5.2.8, 5.2.10, 5.2.11, 5.2.13 and Corollary 5.2.12 (the
formulas of v6_archival.shokri_moura(), checked there against the thesis' Tables 5.6 and 5.7) for every prime power
v <= 25, to the ingredients and as bounds of their own ("SMthm").
Prints both runs and writes ../tables/ladder6.tex (Table S2 with the counts of run B) and ../tables/v6wide.tex
(macros).
"""
import collections
import csv
import io
import math
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
V6 = os.path.dirname(HERE)
CATOOLS = sys.argv[1]
DATA = sys.argv[2] if len(sys.argv) > 2 else os.path.expanduser("~/quantavane-covering-arrays")
OUTDIR = sys.argv[3] if len(sys.argv) > 3 else V6
REF = "ce719cb"
KTAB, KMAX, VMAX = 10000, 100000, 25


def show(path):
    return subprocess.run(["git", "-C", CATOOLS, "show", f"{REF}:{path}"], check=True, capture_output=True).stdout.decode()


def rows(path):
    return list(csv.DictReader(io.StringIO(show(path), newline="")))


def tex(x):
    return f"{int(x):,}".replace(",", "{,}")


def is_pp(v):
    p = 2
    while v % p:
        p += 1
    while v % p == 0:
        v //= p
    return v == 1


def shokri_moura():
    """as v6_archival.shokri_moura(): (v, k, N, theorem)"""
    out = []
    for q in (2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25):
        D = q * q + q + 1
        out.append((q, 2 * D, 4 * q**3 - 5 * q**2 + 2 * q, "5.2.7"))
        if q >= 3:
            out.append((q, q * D, 5 * q**3 - 6 * q**2 + 2 * q, "5.2.8"))
        if q % 2 == 1:
            out.append((q, (q + 1) * D, (12 * q**3 - 13 * q**2 + 5 * q - 2) // 2, "5.2.10"))
        out.append((q, q * q * D, 8 * q**3 - 10 * q**2 + 4 * q - 1, "5.2.11"))
        if q % 2 == 0 or q == 3:
            out.append((q, q * q * D, 8 * q**3 - 10 * q**2 + 3 * q, "5.2.12"))
        out.append((q, (q * q - q + 1) * D, 8 * q**3 - 10 * q**2 + 3 * q, "5.2.13"))
    return out


SM_THM = shokri_moura()
fams = list(csv.DictReader(open(os.path.join(DATA, "families.csv"), newline="")))
big = []
for f in fams:
    t, q, n, k, N = (int(f[x]) for x in ("t", "q", "n", "k", "N"))
    if k > KTAB:
        assert t == 3 and N == n * (q**3 - q) + q
        big.append({"q": q, "n": n, "k": k, "N": N, "name": os.path.basename(f["family"])})
assert len(big) == 35
big_q = sorted({f["q"] for f in big})
table = rows("table/ca_table.csv")


def key(r):
    return (r["t"], r["v"], r["k"], r["N"], r["array_sha256"], r["family_sha256"])


gone = {key(r) for r in table if r["tier"] == "RETRACTED"}
counted = [r for r in table if r["tier"] in ("CITED", "VERIFIED") and not (r["tier"] == "VERIFIED" and key(r) in gone)]
quad = lambda r: (int(r["t"]), int(r["v"]), int(float(r["k"])), int(float(r["N"])))
derived = rows("table/derived.csv")
DCAN = {(int(r["v"]), int(r["k"])): int(r["DCAN_cmtw"]) for r in rows("r/livingtable/data/dcan_table.csv")}
PP = [q for q in range(2, 20000) if is_pp(q)]


def run(with_sm):
    S = {}
    entries = [quad(r) for r in counted] + [(int(d["t"]), int(d["v"]), int(d["k"]), int(d["N"])) for d in derived]
    if with_sm:
        entries += [(3, v, min(k, KMAX), N) for v, k, N, _ in SM_THM]
    for t, v, k, N in entries:
        if t not in (2, 3, 4) or v > VMAX or k > KMAX:
            continue
        a = S.setdefault((t, v), [None] * (KMAX + 2))
        if a[k] is None or N < a[k]:
            a[k] = N
    for a in S.values():
        for k in range(KMAX - 1, -1, -1):
            if a[k + 1] is not None and (a[k] is None or a[k + 1] < a[k]):
                a[k] = a[k + 1]

    def e(t, k, v):
        if t <= 0:
            return 1
        if t == 1:
            return v
        if k < t:
            return 0
        if k == t:
            return v ** t
        a = S.get((t, v))
        return a[k] if a is not None and k <= KMAX else None

    def evaluate(v, ref):
        top = max(ref[KTAB + 1:KMAX + 1])
        S3, S2 = S.get((3, v)), S.get((2, v))
        fuse = [(m, S[(3, v + m)]) for m in range(1, VMAX - v + 1)
                if (3, v + m) in S and S[(3, v + m)][KTAB + 1] is not None and S[(3, v + m)][KTAB + 1] - 2 * m < top]
        comp = [(S.get((3, v1)), S.get((3, v // v1))) for v1 in range(2, math.isqrt(v) + 1) if v % v1 == 0]
        comp = [(a, b) for a, b in comp if a is not None and b is not None]
        S4 = S.get((4, v))
        pct = []
        for q in PP:
            if q > 128 or q > KMAX:
                break
            for ee in range(2, 8):
                M = (ee - 1) * 3 + 1
                if M > q + 1:
                    break
                x = e(3, q, v)
                if x and M * (x - 1) < top:
                    pct.append((q, q ** ee, M))
        kroux = [(h, D, e(3, h, v)) for (vv, h), D in DCAN.items() if vv == v and h >= 3]
        kroux = [(h, D, a) for h, D, a in kroux if a and a + v ** 3 + D * v * v < top]
        sm = None
        if is_pp(v):
            K = v * v + v + 1
            n1 = e(2, K, v)
            n1 = min(n1, 2 * v * v - v) if n1 else 2 * v * v - v
            sm = []
            for n in range(1, 8):
                c = e(3, v ** n, v)
                if c is not None:
                    sm.append((v ** n * K, 2 * v ** 3 + max(n * (v - 1) - 1, 0) * n1 + c))
        smthm = sorted((k, N, th) for vv, k, N, th in SM_THM if vv == v) if with_sm else []
        out = {}
        for k in range(KTAB + 1, KMAX + 1):
            best = (ref[k], None)
            for m, a in fuse:
                x = a[k]
                if x and x - 2 * m < best[0]:
                    best = (x - 2 * m, "fuse")
            if S4 is not None and k + 1 <= KMAX and S4[k + 1] and S4[k + 1] // v < best[0]:
                best = (S4[k + 1] // v, "derive")
            for a, b in comp:
                if a[k] and b[k] and a[k] * b[k] < best[0]:
                    best = (a[k] * b[k], "comp")
            if S3 is not None and S2 is not None:
                h = max(3, (k + 1) // 2)
                if h < k and S3[h] and S2[h] and S3[h] + (v - 1) * S2[h] < best[0]:
                    best = (S3[h] + (v - 1) * S2[h], "CK")
                h = max(3, -(-k // v))
                if S3[h] and S2[h] and S3[h] + (v - 1) * S2[h] + v ** 3 - v ** 2 < best[0]:
                    best = (S3[h] + (v - 1) * S2[h] + v ** 3 - v ** 2, "CMTW34")
                for h, D, a in kroux:
                    l = max(3, -(-k // h))
                    if S3[l] and S2[l] and a + S3[l] + S2[l] * D < best[0]:
                        best = (a + S3[l] + S2[l] * D, "kRoux")
                for q, qe, M in pct:
                    w = q + max(0, k - qe)
                    if w < k and S3[w] and M * (S3[w] - 1) < best[0]:
                        best = (M * (S3[w] - 1), "PCT")
            if sm:
                for kk, N in sm:
                    if kk >= k:
                        if N < best[0]:
                            best = (N, "SM")
                        break
            for kk, N, th in smthm:
                if kk >= k and N < best[0]:
                    best = (N, "SMthm " + th)
            if best[1]:
                out[k] = best
        return out

    counted3 = {}
    for q in big_q:
        a = [None] * (KMAX + 2)
        for t, v, k, N in [quad(r) for r in counted]:
            if t == 3 and v == q and k <= KMAX and (a[k] is None or N < a[k]):
                a[k] = N
        for k in range(KMAX - 1, -1, -1):
            if a[k + 1] is not None and (a[k] is None or a[k + 1] < a[k]):
                a[k] = a[k + 1]
        counted3[q] = a
        assert all(a[k] for k in range(KTAB + 1, KMAX + 1))
    below, rounds = {}, 0
    while True:
        rounds += 1
        changed = 0
        for q in big_q:
            new = evaluate(q, counted3[q])
            if new != below.get(q, {}):
                changed += 1
            below[q] = new
        for q in big_q:
            a = S[(3, q)]
            for k, (N, _) in below[q].items():
                if N < a[k]:
                    a[k] = N
            for k in range(KMAX - 1, KTAB, -1):
                if a[k + 1] is not None and a[k + 1] < a[k]:
                    a[k] = a[k + 1]
        if not changed:
            break
    if not with_sm:  # as version 2: at the table's own widths the result agrees with derived.csv
        for d in derived:
            t, v, k, N = int(d["t"]), int(d["v"]), int(d["k"]), int(d["N"])
            if t == 3 and v in big_q and k > KTAB:
                assert below[v][k][0] == N, (d, below[v].get(k))
    first, yard, runs = collections.Counter(), collections.Counter(), []
    for q in big_q:
        prev = KTAB
        for f in sorted((f for f in big if f["q"] == q), key=lambda f: f["k"]):
            first[f["name"]] = f["k"] - prev
            prev = f["k"]
        for k, (N, law) in sorted(below[q].items()):
            best = min((f for f in big if f["q"] == q and f["k"] >= k), key=lambda f: f["N"])
            if N < best["N"]:
                yard[best["name"]] += 1
                r = runs[-1] if runs else None
                if r and r[0] == q and k == r[2] + 1 and r[3] == law and r[5] == best["N"]:
                    r[2], r[6] = k, N
                else:
                    runs.append([q, k, k, law, N, best["N"], N])
    return first, yard, runs, rounds


def main():
    res = {}
    for tag, with_sm in (("A", False), ("B", True)):
        first, yard, runs, rounds = run(with_sm)
        res[tag] = (first, yard, runs)
        tot_first, tot_yard = sum(first.values()), sum(yard.values())
        print(f"run {tag} ({'with' if with_sm else 'without'} the Shokri-Moura theorem sizes): first entries {tot_first:,}, "
              f"of them above a construction {tot_yard:,} ({100 * (tot_first - tot_yard) / tot_first:.1f}% clear); "
              f"{rounds} rounds")
        for q, a, b, law, lo, ours, hi in runs:
            print(f"  q = {q}: k = {a:,} to {b:,} ({b - a + 1:,} widths): {law}, {lo:,}"
                  f"{'' if hi == lo else ' to ' + format(hi, ',')} rows against our {ours:,}")
    assert sum(res["A"][1].values()) == 11904, "run A must reproduce version 2"
    first, yard, runs = res["B"]
    tot_first, tot_yard = sum(first.values()), sum(yard.values())
    an = collections.defaultdict(str)
    l4 = os.path.join(OUTDIR, "tables", "ladder4.tex")
    for line in (open(l4) if os.path.exists(l4) else []):
        p = [x.strip() for x in line.split("&")]
        if len(p) == 7 and p[0].isdigit():
            an[(int(p[0]), int(p[1]))] = p[4]
    os.makedirs(os.path.join(OUTDIR, "tables"), exist_ok=True)
    L = []
    for f in sorted(big, key=lambda f: (f["q"], f["k"])):
        L.append(f"{f['q']} & {f['n']} & {tex(f['k'])} & {tex(f['N'])} & {an[(f['q'], f['n'])]} & "
                 f"{tex(first[f['name']])} & {tex(yard[f['name']])} \\\\")
    L += [r"\midrule", rf"\multicolumn{{5}}{{l}}{{total, 35 families}} & {tex(tot_first)} & {tex(tot_yard)} \\"]
    open(os.path.join(OUTDIR, "tables", "ladder6.tex"), "w").write("\n".join(L) + "\n")
    pct = 100 * (tot_first - tot_yard) / tot_first
    with open(os.path.join(OUTDIR, "tables", "v6wide.tex"), "w") as fh:
        fh.write("% written by scripts/wide_v6.py\n")
        fh.write("\\newcommand{\\wideFirst}{" + tex(tot_first) + "}\n")
        fh.write("\\newcommand{\\wideAbove}{" + tex(tot_yard) + "}\n")
        fh.write("\\newcommand{\\wideClearPct}{" + f"{pct:.1f}" + "}\n")


if __name__ == "__main__":
    main()
