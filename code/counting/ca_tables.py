"""Covering-array tables: Colbourn's best-known upper bounds on CAN(t,k,v) (t 2-6, v 2-25, k up to 20,000) as dense
arrays, the standard constructions that build large arrays from small ones, and the leverage of each small entry
(how many table cells one fewer row there would improve once the constructions are applied).

The table lists rows (t, v, k, N): CAN(t,k',v) <= N for every k' <= k. Constructions used, each a bound on CAN:
  symbols   CAN(t,k,v) <= CAN(t,k,v+1)                 map symbol v to 0; every tuple over 0..v-1 still appears
  derive    CAN(t-1,k-1,v) <= floor(CAN(t,k,v)/v)      rows holding the rarest symbol of one column, column dropped
  product   CAN(2,k1*k2,v) <= CAN(2,k1,v)+CAN(2,k2,v)  rows of A on column (i,j) read A[.,i], rows of B read B[.,j]
  roux      CAN(3,2k,v) <= CAN(3,k,v)+(v-1)*CAN(2,k,v) Chateauneuf and Kreher, Roux-type doubling for strength 3
The table already applies these and stronger ones, so closure() mostly confirms it; the use is leverage(): which small
entries are worth a search, because an improvement there spreads.
  python3 ca_tables.py [CSV]   prints the closure check and the top leverage cells
"""
import csv
import os
import sys
from collections import defaultdict

import numpy as np

KMAX = 20000
BIG = np.iinfo(np.int64).max // 4
HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT = os.path.join(HERE, "colbournBigFrame.csv")  # not supplied: colbournBigFrame of the CAs R package (Nov 2024)
LATER = os.path.join(HERE, "ca_later.tsv")  # bounds published after the Nov 2024 copy (tables frozen since May 2024)


def load(path=DEFAULT):
    """{(t, v): int64 array B with B[k] = best-known bound on CAN(t,k,v), BIG where the table has no value}."""
    rows = defaultdict(list)
    for r in csv.DictReader(open(path)):
        rows[(int(r["t"]), int(r["v"]))].append((int(float(r["k"])), int(float(r["N"]))))  # the CSV writes 1e+05 for 100000
    tab = {}
    for key, rs in rows.items():
        b = np.full(KMAX + 1, BIG, dtype=np.int64)
        for k, n in rs:
            b[: k + 1] = np.minimum(b[: k + 1], n)  # CAN(t,k',v) <= n for every k' <= k
        b[: key[0]] = BIG  # fewer than t columns: not an entry
        tab[key] = b
    return tab


def load_catools(path):
    """The same from Smolen's live successor table (github.com/chrispbsmolen/ca-tools, table/ca_table.csv), which holds
    the Nov 2024 copy as its CITED rows plus later papers and verified arrays: only its CITED and VERIFIED rows, the ones
    it counts as best known, at t 2-6 and v 2-25."""
    rows = defaultdict(list)
    for r in csv.DictReader(open(path, newline="")):
        t, v = int(r["t"]), int(r["v"])
        if r["tier"] in ("CITED", "VERIFIED") and 2 <= t <= 6 and 2 <= v <= 25:
            rows[(t, v)].append((min(int(float(r["k"])), KMAX), int(float(r["N"]))))
    tab = {}
    for key, rs in rows.items():
        b = np.full(KMAX + 1, BIG, dtype=np.int64)
        for k, n in rs:
            b[: k + 1] = np.minimum(b[: k + 1], n)
        b[: key[0]] = BIG
        tab[key] = b
    return tab


def load_later(tab, path=LATER):
    """Lower the table by bounds published after the Nov 2024 copy: each line t, v, k, N of ca_later.tsv
    says CAN(t,k',v) <= N for every k' <= k (only cells the table lists, k' >= t). Returns tab."""
    for line in open(path):
        if not line[:1].isdigit():
            continue
        t, v, k, n = (int(x) for x in line.split("\t")[:4])
        b = tab[(t, v)]
        b[t : k + 1] = np.minimum(b[t : k + 1], n)
    return tab


def step(tab):
    """One round of every construction; returns {(t, v): implied bound array} (BIG where nothing is implied)."""
    out = {key: np.full(KMAX + 1, BIG, dtype=np.int64) for key in tab}
    for (t, v), b in tab.items():
        if (t, v - 1) in out:  # symbols: an array over v symbols serves v-1
            np.minimum(out[(t, v - 1)], b, out=out[(t, v - 1)])
        if t > 2 and (t - 1, v) in out:  # derive: CAN(t-1,k-1,v) <= floor(CAN(t,k,v)/v)
            d = np.where(b[1:] < BIG, b[1:] // v, BIG)
            np.minimum(out[(t - 1, v)][:-1], d, out=out[(t - 1, v)][:-1])
        if t == 2:  # product: CAN(2,k1*k2,v) <= CAN(2,k1,v) + CAN(2,k2,v)
            o = out[(2, v)]
            for k1 in range(2, int(KMAX ** 0.5) + 1):
                if b[k1] >= BIG:
                    continue
                k2 = np.arange(k1, KMAX // k1 + 1)
                ok = b[k2] < BIG
                np.minimum.at(o, k1 * k2[ok], b[k1] + b[k2[ok]])
        if t == 3 and (2, v) in tab:  # roux: CAN(3,2k,v) <= CAN(3,k,v) + (v-1) CAN(2,k,v)
            b2 = tab[(2, v)]
            k = np.arange(3, KMAX // 2 + 1)
            ok = (b[k] < BIG) & (b2[k] < BIG)
            np.minimum.at(out[(3, v)], 2 * k[ok], b[k[ok]] + (v - 1) * b2[k[ok]])
    for key, o in out.items():  # a bound for k columns holds for fewer columns
        o[:] = np.minimum.accumulate(o[::-1])[::-1]
        o[: key[0]] = BIG
    return out


def closure(tab, rounds=50):
    """Apply the constructions until nothing changes; returns (closed table, rounds used)."""
    cur = {key: b.copy() for key, b in tab.items()}
    for r in range(1, rounds + 1):
        imp = step(cur)
        changed = False
        for key in cur:
            better = imp[key] < cur[key]
            if better.any():
                cur[key] = np.minimum(cur[key], imp[key])
                changed = True
        if not changed:
            return cur, r
    return cur, rounds


def improved_cells(base, closed, within=None):
    """Number of (t, v, k) cells where closed is below base, and the total row saving. Only cells the table lists
    count: pass the table itself as within when base is its closure, since the constructions (roux doubling) carry
    bounds past the table's last k, and those cells are not in it."""
    n = s = 0
    for key, b in base.items():
        d = (closed[key] < b) & ((within if within is not None else base)[key] < BIG)
        n += int(d.sum())
        s += int((b - closed[key])[d].sum())
    return n, s


def leverage(tab, t, v, k, closed=None):
    """Cells improved if CAN(t,k,v) were one row below the table (with the constructions applied)."""
    base = closed if closed is not None else closure(tab)[0]
    trial = {key: b.copy() for key, b in base.items()}
    trial[(t, v)][: k + 1] = np.minimum(trial[(t, v)][: k + 1], base[(t, v)][k] - 1)
    after, _ = closure(trial)
    return improved_cells(base, after, tab)[0]


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT
    tab = load(path)
    cells = sum(int((b < BIG).sum()) for b in tab.values())
    print(f"{len(tab)} (t,v) tables, {cells:,} cells with a bound")
    closed, r = closure(tab)
    n, s = improved_cells(tab, closed)
    print(f"closure under symbols/derive/product/roux: {r} rounds, {n:,} cells below the table (total {s:,} rows)")


if __name__ == "__main__":
    main()
