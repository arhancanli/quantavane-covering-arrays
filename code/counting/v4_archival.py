"""Version 4: every count of the paper against the ARCHIVAL baseline (Major issue 3(a)), and the per-family columns
asked for in Major issues 1 and 2.

    OUT=out python3 v4_archival.py DATA CATOOLS        (python3 with numpy; imports ca_tables.py from this folder)

DATA     local clone of github.com/arhancanli/quantavane-covering-arrays, read at commit ea668c0 (git show)
CATOOLS  clone of github.com/chrispbsmolen/ca-tools, read at commit ce719cb (data file table/ca_table.csv only)

Baseline ("archival"): the CITED rows of the ca-tools table at ce719cb whose snapshot is the November 2024 copy of
Colbourn's tables (colbourn-2024-11-ug) or the one peer-reviewed later source the table holds, Torres-Jimenez and
Izquierdo-Marquez 2024 (doi:10.3390/math12121908); no row of ours, no other later source. "Before" is its closure under
the standard constructions (ca_tables.closure: fewer columns, symbol deletion, derivation, strength-2 product,
Roux doubling); "after" is the same closure with our 161 families of at most 10,000 columns added. A cell (t, v, k),
3 <= t <= 6, 2 <= v <= 25, t <= k <= 10,000, counts when the baseline lists a size there and "after" < "before".

Writes OUT/data/arch_cells.csv, OUT/data/arch_families.csv, OUT/data/arch_rep.csv and the macro file OUT/v4arch.tex, and
prints every number with a label.
"""
import collections
import csv
import io
import math
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
V4 = os.environ.get("OUT", "out")  # output folder (release copy: was the paper's version folder)
os.makedirs(os.path.join(V4, "data"), exist_ok=True)
DATA, CATOOLS = sys.argv[1], sys.argv[2]
LIVE, DATA_COMMIT, DOI = "ce719cb", "ea668c0", "23839216"
ARCH_SNAPSHOTS = ("colbourn-2024-11-ug", "doi:10.3390/math12121908")
sys.path.insert(0, HERE)
import numpy as np  # noqa: E402
import ca_tables as T  # noqa: E402

BIG, KMAX = T.BIG, 10000
# the five strength-6 families the table checked on prefixes only: (q, prefix)
PREFIX = {(6, 9, 5000): 3950, (6, 11, 5000): 4200, (6, 13, 5000): 4400, (6, 16, 5000): 4800, (6, 17, 5000): 4900}
KINDS = [  # as in v2's prior_methods.py: (kind, regular expression on the reduced label), first match wins
    ("cphf", r"CPHF|SCPHF|covering perfect hash"),
    ("phf", r"^perfect hash family"),
    ("power", r"^Power (N-)?CT"),
    ("roux", r"Martirosyan|Chateauneuf|Cohen-Colbourn-Ling|Roux|doubling"),
    ("add", r"^Add (a|\d+) factors?|Derive|Power CZ|product|Product"),
    ("oa", r"orthogonal array|Augment OA|extended OA|OA\b"),
    ("cyclic", r"[Cc]yclotomy|[Cc]yclic"),
    ("search", r"IPOG|annealing|Annealing|tabu|Tabu|Torres Jimenez|Torres-Jimenez|Dwyer|greedy|Greedy|search|Search"),
]


def show(repo, ref, path):
    return subprocess.run(["git", "-C", repo, "show", f"{ref}:{path}"], check=True, capture_output=True).stdout.decode()


def reduce_label(label):
    return re.sub(r"(\s+fuse|\s+postop.*)+$", "", label.strip())


def kind(label):
    for kd, rx in KINDS:
        if re.search(rx, label):
            return kd
    return "other"


def main():
    rows = [r for r in csv.DictReader(io.StringIO(show(CATOOLS, LIVE, "table/ca_table.csv"), newline=""))
            if r["tier"] == "CITED" and r["snapshot_id"] in ARCH_SNAPSHOTS and DOI not in r["source_detail"]]
    tab = collections.defaultdict(lambda: np.full(T.KMAX + 1, BIG, dtype=np.int64))
    entries = collections.defaultdict(list)  # (t, v) -> [(k, N, label)]
    for r in rows:
        t, v, k, N = int(r["t"]), int(r["v"]), int(float(r["k"])), int(float(r["N"]))
        if not (2 <= t <= 6 and 2 <= v <= 25):
            continue
        kk = min(k, T.KMAX)
        b = tab[(t, v)]
        b[: kk + 1] = np.minimum(b[: kk + 1], N)
        entries[(t, v)].append((k, N, reduce_label(r["construction"] or r["source_detail"])))
    for (t, v), b in tab.items():
        b[:t] = BIG
    for t in range(2, 7):
        for v in range(2, 26):
            tab[(t, v)]  # every key present
    tab = dict(tab)
    print(f"archival rows used: {sum(len(x) for x in entries.values())} (CITED, snapshots {', '.join(ARCH_SNAPSHOTS)})")
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
    import bisect
    sorted_entries = {key: sorted(es) for key, es in entries.items()}
    ent_k = {key: [e[0] for e in es] for key, es in sorted_entries.items()}

    def label_at(key, k):  # label of the table entry that gives the listed size at k (fewest columns, then label)
        es = sorted_entries.get(key, [])
        i = bisect.bisect_left(ent_k.get(key, []), k)
        best = None
        for e in es[i:]:
            if e[1] == tab[key][k]:
                if best is None or e[0] == best[0]:
                    best = e if best is None or e[2] < best[2] else best
                else:
                    break
        return best[2] if best else "?"

    fam_by_key = collections.defaultdict(list)
    for f in small:
        fam_by_key[(int(f["t"]), int(f["q"]))].append(f)
    # every improved cell
    cells = []
    for t in range(3, 7):
        for v in range(2, 26):
            key = (t, v)
            for k in range(t, KMAX + 1):
                if tab[key][k] >= BIG or after[key][k] >= before[key][k]:
                    continue
                direct = [f for f in fam_by_key[key] if int(f["k"]) >= k and int(f["N"]) == after[key][k]]
                lab = label_at(key, k)
                cells.append({"t": t, "v": v, "k": k, "table": int(tab[key][k]), "before": int(before[key][k]),
                              "N": int(after[key][k]), "how": ("direct " + direct[0]["family"].split("/")[-1]) if direct else "derived",
                              "prior_label": lab, "prior_kind": kind(lab)})
    n = len(cells)
    by_t = collections.Counter(c["t"] for c in cells)
    nd = sum(c["how"].startswith("direct") for c in cells)
    sav = [(c["before"] - c["N"]) / c["before"] for c in cells]
    print(f"ARCHIVAL STANDARD: {n} cells improved; by t {dict(sorted(by_t.items()))}; direct {nd}, derived {n - nd}; "
          f"median relative saving {100 * float(np.median(sav)):.1f}%")
    with open(os.path.join(V4, "data", "arch_cells.csv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(cells[0].keys()))
        w.writeheader()
        w.writerows(cells)

    # families: direct improvements, previous best size at their width, previous width at their size
    famrows, improving = [], 0
    for f in small:
        t, v, K, N, nrows = int(f["t"]), int(f["q"]), int(f["k"]), int(f["N"]), int(f["n"])
        key = (t, v)
        imp = sum(1 for k in range(t, K + 1) if tab[key][k] < BIG and after[key][k] == N < before[key][k])
        improving += imp > 0
        nb = int(before[key][K])
        lab = label_at(key, K)
        ks = np.nonzero(before[key][: KMAX + 1] <= N)[0]
        kb = int(ks.max()) if ks.size else 0
        famrows.append({"t": t, "q": v, "n": nrows, "k": K, "N": N, "before_N_at_k": nb,
                        "saving_pct": round(100 * (nb - N) / nb, 2), "before_label_at_k": lab, "before_kind_at_k": kind(lab),
                        "before_width_at_N": kb, "width_gain_pct": round(100 * (K / kb - 1), 2) if kb else "",
                        "direct_cells": imp})
    print(f"families with at most 10,000 columns that improve at least one cell directly: {improving} of {len(small)}")
    for fr in famrows:
        if not fr["direct_cells"]:
            print(f"  improves no cell directly: t {fr['t']} q {fr['q']} n {fr['n']} k {fr['k']} N {fr['N']} "
                  f"(before at k: {fr['before_N_at_k']}, {fr['before_label_at_k']})")
    with open(os.path.join(V4, "data", "arch_families.csv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(famrows[0].keys()))
        w.writeheader()
        w.writerows(famrows)

    # by (t, v)
    S1 = []
    byk = collections.defaultdict(list)
    for c in cells:
        byk[(c["t"], c["v"])].append(c)
    for key in sorted(byk):
        cs = byk[key]
        s = sorted((c["before"] - c["N"]) / c["before"] for c in cs)
        S1.append((key[0], key[1], sum(1 for f in small if (int(f["t"]), int(f["q"])) == key), len(cs),
                   sum(not c["how"].startswith("direct") for c in cs), min(c["k"] for c in cs), max(c["k"] for c in cs),
                   100 * float(np.median(s)), 100 * s[-1]))
    with open(os.path.join(V4, "data", "arch_by_tv.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["t", "v", "families", "cells", "derived", "k_min", "k_max", "median_saving_pct", "largest_saving_pct"])
        for r in S1:
            w.writerow([r[0], r[1], r[2], r[3], r[4], r[5], r[6], f"{r[7]:.1f}", f"{r[8]:.1f}"])
    for r in S1:
        print("  by (t,v): t %d v %2d: families %d, cells %d, derived %d, k %d-%d, median %.1f%%, largest %.1f%%" % r)

    # prior kinds
    kinds = collections.Counter(c["prior_kind"] for c in cells)
    kd_direct = collections.Counter(c["prior_kind"] for c in cells if c["how"].startswith("direct"))
    kd_sav = collections.defaultdict(list)
    for c in cells:
        kd_sav[c["prior_kind"]].append((c["before"] - c["N"]) / c["before"])
    for kd in ("cphf", "phf", "power", "roux", "add", "oa", "cyclic", "search", "other"):
        if kinds[kd]:
            print(f"  prior kind {kd:7s}: {kinds[kd]} cells, {kd_direct[kd]} direct, median saving {100 * float(np.median(kd_sav[kd])):.1f}%")
    labs = collections.Counter((c["prior_kind"], c["prior_label"]) for c in cells)
    pw = [(lab, n_) for (kd, lab), n_ in labs.items() if kd == "power"]
    print("  power labels:", sorted(pw, key=lambda x: -x[1])[:4])

    # representative bounds
    rep = []
    for t in range(3, 7):
        for v in range(4, 26):
            for k in (100, 1000, 5000, 10000):
                if k < t or tab[(t, v)][k] >= BIG:
                    continue
                lab = label_at((t, v), k)
                rep.append({"t": t, "v": v, "k": k, "before": int(before[(t, v)][k]), "after": int(after[(t, v)][k]),
                            "table": int(tab[(t, v)][k]), "prior_label": lab, "prior_kind": kind(lab)})
    with open(os.path.join(V4, "data", "arch_rep.csv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rep[0].keys()))
        w.writeheader()
        w.writerows(rep)

    # cells that rest on our check alone: the five prefix families cut to their checked prefixes
    cut = []
    for f in small:
        key3 = (int(f["t"]), int(f["q"]), int(f["k"]))
        g = dict(f)
        if key3 in PREFIX:
            g["k"] = str(PREFIX[key3])
        cut.append(g)
    after_cut = closure_with(cut)
    lost = worse = 0
    dep_t = collections.Counter()
    for c in cells:
        key, k = (c["t"], c["v"]), c["k"]
        a2 = after_cut[key][k]
        if a2 >= before[key][k]:
            lost += 1
            dep_t[c["t"]] += 1
        elif a2 > c["N"]:
            worse += 1
            dep_t[c["t"]] += 1
    print(f"with the five strength-6 families cut to their checked prefixes: {lost + worse} cells lost or larger "
          f"({lost} no longer improved, {worse} improved by less); by t {dict(sorted(dep_t.items()))}")
    # also without the ten families that have no VERIFIED row in the table (never checked by its program)
    unchecked = {(3, 7, 4, 234), (3, 7, 5, 619), (4, 7, 4, 62), (4, 7, 6, 207), (4, 7, 7, 379), (5, 7, 26, 3000),
                 (5, 9, 16, 6560), (5, 9, 17, 6560), (5, 11, 22, 10000), (6, 19, 15, 1000)}
    cut2 = [g for g in cut if (int(g["t"]), int(g["q"]), int(g["n"]), int(g["k"]) if (int(g["t"]), int(g["q"]), int(g["k"])) not in PREFIX
                               else int([f for f in small if f["family"] == g["family"]][0]["k"])) not in unchecked]
    assert len(cut2) == 151, len(cut2)
    after_cut2 = closure_with(cut2)
    lost2 = worse2 = 0
    dep2_t = collections.Counter()
    for c in cells:
        key, k = (c["t"], c["v"]), c["k"]
        a2 = after_cut2[key][k]
        if a2 >= before[key][k]:
            lost2 += 1
            dep2_t[c["t"]] += 1
        elif a2 > c["N"]:
            worse2 += 1
            dep2_t[c["t"]] += 1
    print(f"also without the 10 families the table never checked: {lost2 + worse2} cells lost or larger "
          f"({lost2} no longer improved, {worse2} improved by less); by t {dict(sorted(dep2_t.items()))}")

    # macros
    def tex(x):
        return f"{int(x):,}".replace(",", "{,}")
    M = {"aCells": tex(n), "aCellsTThree": tex(by_t[3]), "aCellsTFour": tex(by_t[4]), "aCellsTFive": tex(by_t[5]),
         "aCellsTSix": tex(by_t[6]), "aDirect": tex(nd), "aDerived": tex(n - nd), "aMedian": f"{100 * float(np.median(sav)):.1f}\\%",
         "aFamImproving": str(improving), "aRows": tex(sum(len(x) for x in entries.values())),
         "aDep": tex(lost + worse), "aDepLost": tex(lost), "aDepWorse": tex(worse),
         "aDepTSix": tex(dep_t[6]), "aDepTFive": tex(dep_t[5]),
         "aDepAll": tex(lost2 + worse2), "aDepAllLost": tex(lost2), "aDepAllWorse": tex(worse2),
         "aCphf": tex(kinds["cphf"]), "aCphfMed": f"{100 * float(np.median(kd_sav['cphf'])):.1f}\\%"}
    with open(os.path.join(V4, "v4arch.tex"), "w") as fh:
        fh.write("% written by scripts/v4_archival.py (archival baseline: CITED rows of ca-tools ce719cb, snapshots "
                 "colbourn-2024-11-ug and doi:10.3390/math12121908; families.csv at ea668c0)\n")
        for name, val in M.items():
            fh.write("\\newcommand{\\%s}{%s}\n" % (name, val))
    for name, val in M.items():
        print(f"  macro {name} = {val}")


if __name__ == "__main__":
    main()
