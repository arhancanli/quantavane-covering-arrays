"""Cells that rest on our checks alone, given the second checks that are complete when this runs (Section 7).

    python3 dependent_v5.py DATA CATOOLS [STATUS_JSON [OUT_JSON]]        (python3 with numpy)

DATA     the data repository (github.com/arhancanli/quantavane-covering-arrays), read at commit 6183ffe (git show);
         its folder code/counting supplies the closure (ca_tables.py)
CATOOLS  a clone of github.com/chrispbsmolen/ca-tools, read at commit ce719cb (data file table/ca_table.csv only)

The archival baseline and the closure are exactly those of v4_archival.py (code/counting): the CITED rows of the table
whose snapshot is the November 2024 copy of Colbourn's tables or doi:10.3390/math12121908, closed under the standard
constructions; "after" adds our 161 families of at most 10,000 columns. Here "after" is recomputed with
  - each strength-6 family whose second check is not complete (data/second_checks_status.json, written by
    second_checks.py) cut to the prefix that the ca-tools table checked, and
  - the ten families with at most 10,000 columns that the table never checked left out,
and an improved cell rests on our checks alone when it is lost or improved by less. Writes OUT_JSON (default
../data/dependent.json); STATUS_JSON defaults to ../data/second_checks_status.json (paths relative to this script).
"""
import collections
import csv
import io
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
V5 = os.path.dirname(HERE)
DATA, CATOOLS = sys.argv[1], sys.argv[2]
LIVE, DATA_COMMIT, DOI = "ce719cb", "6183ffe", "23839216"
ARCH_SNAPSHOTS = ("colbourn-2024-11-ug", "doi:10.3390/math12121908")
sys.path.insert(0, os.path.join(DATA, "code", "counting"))
import numpy as np  # noqa: E402
import ca_tables as T  # noqa: E402

BIG, KMAX = T.BIG, 10000
PREFIX = {9: 3950, 11: 4200, 13: 4400, 16: 4800, 17: 4900}  # strength 6, 5,000 columns: the table's checked prefixes
UNCHECKED = {(3, 7, 4, 234), (3, 7, 5, 619), (4, 7, 4, 62), (4, 7, 6, 207), (4, 7, 7, 379), (5, 7, 26, 3000),
             (5, 9, 16, 6560), (5, 9, 17, 6560), (5, 11, 22, 10000), (6, 19, 15, 1000)}


def show(repo, ref, path):
    return subprocess.run(["git", "-C", repo, "show", f"{ref}:{path}"], check=True, capture_output=True).stdout.decode()


def main():
    status_path = sys.argv[3] if len(sys.argv) > 3 else os.path.join(V5, "data", "second_checks_status.json")
    out_path = sys.argv[4] if len(sys.argv) > 4 else os.path.join(V5, "data", "dependent.json")
    status = json.load(open(status_path))
    pending = sorted(int(q) for q, s in status.items() if s["verdict"] != "PASS")
    rows = [r for r in csv.DictReader(io.StringIO(show(CATOOLS, LIVE, "table/ca_table.csv"), newline=""))
            if r["tier"] == "CITED" and r["snapshot_id"] in ARCH_SNAPSHOTS and DOI not in r["source_detail"]]
    tab = collections.defaultdict(lambda: np.full(T.KMAX + 1, BIG, dtype=np.int64))
    for r in rows:
        t, v, k, N = int(r["t"]), int(r["v"]), int(float(r["k"])), int(float(r["N"]))
        if not (2 <= t <= 6 and 2 <= v <= 25):
            continue
        kk = min(k, T.KMAX)
        b = tab[(t, v)]
        b[: kk + 1] = np.minimum(b[: kk + 1], N)
    for (t, v), b in tab.items():
        b[:t] = BIG
    for t in range(2, 7):
        for v in range(2, 26):
            tab[(t, v)]
    tab = dict(tab)
    before, _ = T.closure(tab)
    fams = list(csv.DictReader(io.StringIO(show(DATA, DATA_COMMIT, "families.csv"), newline="")))
    small = [f for f in fams if int(f["k"]) <= 10000]
    assert len(small) == 161, len(small)

    def closure_with(fs):
        trial = {key: b.copy() for key, b in tab.items()}
        for f in fs:
            t, v, K, N = int(f["t"]), int(f["q"]), int(f["k"]), int(f["N"])
            trial[(t, v)][: K + 1] = np.minimum(trial[(t, v)][: K + 1], N)
        return T.closure(trial)[0]

    after = closure_with(small)
    cells = []
    for t in range(3, 7):
        for v in range(2, 26):
            key = (t, v)
            for k in range(t, KMAX + 1):
                if tab[key][k] < BIG and after[key][k] < before[key][k]:
                    cells.append((key, k, int(after[key][k])))
    print(f"archival improved cells: {len(cells)} (version 4: 461,352)")
    cut = []
    for f in small:
        t, q, n, k = int(f["t"]), int(f["q"]), int(f["n"]), int(f["k"])
        if (t, q, n, k) in UNCHECKED:
            continue
        g = dict(f)
        if t == 6 and k == 5000 and q in pending:
            g["k"] = str(PREFIX[q])
        cut.append(g)
    after_cut = closure_with(cut)
    lost = worse = 0
    by_t = collections.Counter()
    for key, k, N in cells:
        a2 = after_cut[key][k]
        if a2 >= before[key][k]:
            lost += 1
            by_t[key[0]] += 1
        elif a2 > N:
            worse += 1
            by_t[key[0]] += 1
    out = {"pending_q": pending, "cells": lost + worse, "lost": lost, "worse": worse, "total": len(cells),
           "by_t": dict(sorted(by_t.items())), "families_used": len(cut)}
    print(json.dumps(out))
    json.dump(out, open(out_path, "w"), indent=1)


if __name__ == "__main__":
    main()
