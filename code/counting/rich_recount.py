"""Recounts of the improved cells for v3 (Major issue 5, Question 7): a richer closure and an archival baseline.

    python3 rich_recount.py DATA CATOOLS        (python3 with numpy; imports ca_tables.py from this folder)

Baselines (rows of the ca-tools table at commit ce719cb, tiers CITED and VERIFIED, t 2-6, v 2-25, without the rows
that cite our release):
  LIVE      every such row, lowered by the later bounds of ca_later.tsv and by Table 5.6 of Shokri's
            thesis: the baseline of v2 (448,049 cells);
  ARCHIVAL  only the rows of the November 2024 copy of Colbourn's tables (snapshot colbourn-2024-11-ug) and of the one
            peer-reviewed later source the table holds, Torres-Jimenez and Izquierdo-Marquez 2024 (Mathematics 12, 1908);
            no other later bound.
Closures (applied to "before" and, with our families added, to "after", identically):
  STANDARD  ca_tables.closure: fewer columns, symbol deletion, derivation, strength-2 product, Roux doubling;
  RICH      STANDARD plus, until nothing changes:
              fusion   CAN(t,k,v) <= CAN(t,k,v+1) - 2 (Colbourn, Keri, Rivas Soriano and Schlage-Puchta 2010; every t)
              product  CAN(t,k,v1 v2) <= CAN(t,k,v1) CAN(t,k,v2) (every t)
              and at strength 3 the laws of the yardstick of v2 (make_table_v2.evaluate), now at every k <= 20,000:
              CMTW Thm 3.4, k-ary Roux with the DCAN values of the table's dcan_table.csv, the power construction
              (established part, as in v2) and Shokri-Moura.
A cell counts when "after" is below "before" and the baseline table lists the cell (as in v2). The RICH closure of the
full live table (our rows included) is checked against the table's own computed sizes (derived.csv, k <= 10,000):
it must be at most each of them.
"""
import csv
import io
import math
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
DATA, CATOOLS = sys.argv[1], sys.argv[2]
LIVE, DATA_COMMIT, DOI = "ce719cb", "ea668c0", "23839216"
T56 = os.path.join(HERE, "shokri_thesis_table56.tsv")
sys.path.insert(0, HERE)
import numpy as np  # noqa: E402
import ca_tables as T  # noqa: E402

BIG, KMAX = T.BIG, T.KMAX
CAP = 10 ** 15  # products above this are ignored (no cell is that large)


def show(repo, ref, path):
    return subprocess.run(["git", "-C", repo, "show", f"{ref}:{path}"], check=True, capture_output=True).stdout.decode()


def is_pp(v):
    p = 2
    while v % p:
        p += 1
    while v % p == 0:
        v //= p
    return v == 1


ALL = list(csv.DictReader(io.StringIO(show(CATOOLS, LIVE, "table/ca_table.csv"), newline="")))
DCAN = {}
for r in csv.DictReader(io.StringIO(show(CATOOLS, LIVE, "r/livingtable/data/dcan_table.csv"), newline="")):
    DCAN[(int(r["v"]), int(r["k"]))] = int(r["DCAN_cmtw"])


def table(rows, later):
    with tempfile.NamedTemporaryFile("w", suffix=".csv", newline="", delete=False) as f:
        w = csv.DictWriter(f, fieldnames=list(ALL[0].keys()))
        w.writeheader()
        w.writerows(rows)
    tab = T.load_catools(f.name)
    os.unlink(f.name)
    if later:
        tab = T.load_later(tab)
        tab = T.load_later(tab, T56)
    return tab


def cur_lookup(b, k):
    return b[k] if 0 <= k <= KMAX else BIG


def rich_step(cur):
    out = {key: np.full(KMAX + 1, BIG, dtype=np.int64) for key in cur}
    for (t, v), b in cur.items():
        # fusion from v+1 to v
        if (t, v + 1) in cur and v >= 2:
            s = cur[(t, v + 1)]
            ok = s < BIG
            o = out[(t, v)]
            o[ok] = np.minimum(o[ok], s[ok] - 2)
        # product of alphabets
        for v1 in range(2, math.isqrt(v) + 1):
            if v % v1 == 0 and (t, v1) in cur and (t, v // v1) in cur:
                a, c = cur[(t, v1)], cur[(t, v // v1)]
                ok = (a < BIG) & (c < BIG) & (a < CAP // np.maximum(c, 1))
                o = out[(t, v)]
                o[ok] = np.minimum(o[ok], a[ok] * c[ok])
    for v in range(2, 26):
        if (3, v) not in cur or (2, v) not in cur:
            continue
        S3, S2, o = cur[(3, v)], cur[(2, v)], out[(3, v)]
        ks = np.arange(KMAX + 1)
        # CMTW Theorem 3.4: CAN(3, k, v) <= CAN(3,h,v) + (v-1) CAN(2,h,v) + v^3 - v^2, h = max(3, ceil(k/v))
        h = np.maximum(3, -(-ks // v))
        ok = (ks >= 4) & (h < ks) & (S3[np.minimum(h, KMAX)] < BIG) & (S2[np.minimum(h, KMAX)] < BIG)
        val = S3[np.minimum(h, KMAX)] + (v - 1) * S2[np.minimum(h, KMAX)] + v ** 3 - v ** 2
        o[ok] = np.minimum(o[ok], val[ok])
        # k-ary Roux with the DCAN values: CAN(3, l h, v) <= CAN(3,h,v) + CAN(3,l,v) + D CAN(2,l,v), l = max(3, ceil(k/h))
        for (vv, hh), D in DCAN.items():
            if vv != v or hh < 3 or hh > KMAX or S3[hh] >= BIG:
                continue
            l = np.maximum(3, -(-ks // hh))
            lc = np.minimum(l, KMAX)
            ok = (ks >= 4) & (l < ks) & (S3[lc] < BIG) & (S2[lc] < BIG)
            val = S3[hh] + S3[lc] + D * S2[lc]
            o[ok] = np.minimum(o[ok], val[ok])
        # power construction, established part, as in v2's yardstick
        for qq in (x for x in range(2, 129) if is_pp(x)):
            for ee in range(2, 8):
                M = (ee - 1) * 3 + 1
                if M > qq + 1 or qq ** ee > 10 ** 7:
                    break
                w = qq + np.maximum(0, ks - qq ** ee)
                wc = np.minimum(w, KMAX)
                ok = (ks >= 4) & (w < ks) & (S3[wc] < BIG)
                val = M * (S3[wc] - 1)
                o[ok] = np.minimum(o[ok], val[ok])
        # Shokri and Moura, prime-power v: k <= v^n (v^2+v+1)
        if is_pp(v):
            K = v * v + v + 1
            n1 = int(S2[K]) if K <= KMAX and S2[K] < BIG else BIG
            n1 = min(n1, 2 * v * v - v)
            prev = 3
            for n in range(1, 8):
                kk = v ** n * K
                if v ** n > KMAX or S3[v ** n] >= BIG:
                    break
                N = 2 * v ** 3 + max(n * (v - 1) - 1, 0) * n1 + int(S3[v ** n])
                lo, hi = prev + 1, min(kk, KMAX)
                if lo <= hi:
                    o[lo:hi + 1] = np.minimum(o[lo:hi + 1], N)
                prev = kk
                if kk >= KMAX:
                    break
    for key, o in out.items():
        o[:] = np.minimum.accumulate(o[::-1])[::-1]
        o[: key[0]] = BIG
    return out


def rich_closure(tab):
    cur, _ = T.closure(tab)
    for _ in range(60):
        imp = rich_step(cur)
        changed = False
        for key in cur:
            better = imp[key] < cur[key]
            if better.any():
                cur[key] = np.minimum(cur[key], imp[key])
                changed = True
        if not changed:
            return cur
        cur, _ = T.closure(cur)
    raise RuntimeError("rich closure did not settle")


FAMS = list(csv.DictReader(io.StringIO(show(DATA, DATA_COMMIT, "families.csv"), newline="")))


def count(tab, rich):
    clo = rich_closure if rich else (lambda x: T.closure(x)[0])
    base = clo(tab)
    trial = {key: b.copy() for key, b in tab.items()}
    for r in FAMS:
        t, v, K, N = int(r["t"]), int(r["q"]), min(int(r["k"]), KMAX), int(r["N"])
        trial[(t, v)][: K + 1] = np.minimum(trial[(t, v)][: K + 1], N)
    after = clo(trial)
    n, by_t, direct_like = 0, {}, 0
    savings = []
    for key in sorted(base):
        d = (after[key] < base[key]) & (tab[key] < BIG)
        c = int(d.sum())
        n += c
        by_t[key[0]] = by_t.get(key[0], 0) + c
        if c:
            savings.extend(((base[key][d] - after[key][d]) / base[key][d]).tolist())
    med = float(np.median(savings)) if savings else 0.0
    return n, by_t, med


def main():
    ours = lambda r: DOI in r["source_detail"]  # noqa: E731
    live_rows = [r for r in ALL if not ours(r)]
    arch_rows = [r for r in ALL if not ours(r) and r["tier"] == "CITED"
                 and r["snapshot_id"] in ("colbourn-2024-11-ug", "doi:10.3390/math12121908")]
    # validation of the rich closure against the table's own computed sizes (our rows included)
    full = rich_closure(table(ALL, False))
    bad = checked = 0
    for d in csv.DictReader(io.StringIO(show(CATOOLS, LIVE, "table/derived.csv"), newline="")):
        t, v, k, N = int(d["t"]), int(d["v"]), int(d["k"]), int(d["N"])
        if 3 <= t <= 6 and 2 <= v <= 25 and k <= 10000:
            checked += 1
            bad += int(full[(t, v)][k] > N)
    print(f"rich closure of the full live table at most the table's computed size at {checked - bad} of {checked} "
          f"points of derived.csv with k <= 10,000")
    for name, rows, later in (("LIVE", live_rows, True), ("ARCHIVAL", arch_rows, False)):
        for rich in (False, True):
            n, by_t, med = count(table(rows, later), rich)
            print(f"{name:8s} {'RICH' if rich else 'STANDARD':8s}: {n} cells improved; by t {dict(sorted(by_t.items()))}; "
                  f"median relative saving {100 * med:.1f}%", flush=True)
    print(f"archival rows: {len(arch_rows)} (Colbourn November 2024 copy and Torres-Jimenez-Izquierdo-Marquez 2024)")


if __name__ == "__main__":
    main()
