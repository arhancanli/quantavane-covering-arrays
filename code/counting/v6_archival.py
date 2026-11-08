"""Version 6: every count against the archival baseline, with the refereed strength-3 sizes of Shokri and Moura (2025)
added to the baseline, the families whose second check is not complete cut to their doubly checked prefixes, and the
23-row q = 8 family (first 3,171 columns) added once its second check has passed.

    python3 v6_archival.py DATA CATOOLS STATUS_JSON OUTDIR        (python3 with numpy; ca_tables.py from this folder)

DATA        the data repository (working tree: families.csv and the family files)
CATOOLS     a clone of github.com/chrispbsmolen/ca-tools containing commit ce719cb (data file table/ca_table.csv only)
STATUS_JSON second_checks_status.json written by second_checks_v6.py (verdicts of the tails of q = 9, 11, 13, 16, 17
            and of the second check of the q = 8 prefix family)
OUTDIR      output folder: OUTDIR/data/arch_*.csv and OUTDIR/tables/v6arch.tex

Baseline ("archival"): the CITED rows of the ca-tools table at ce719cb whose snapshot is the November 2024 copy of
Colbourn's tables (colbourn-2024-11-ug) or Torres-Jimenez and Izquierdo-Marquez 2024 (doi:10.3390/math12121908), and
the strength-3 families of Shokri and Moura, J. Combin. Des. 33 (2025) 156-171, generated from the closed formulas of
their theorems (Theorems 5.2.7, 5.2.8, 5.2.10, 5.2.11, 5.2.13 and Corollary 5.2.12 of Shokri's thesis, Chapter 5 of
which is that paper) for every prime power 2 <= q <= 25 and checked against the thesis' Tables 5.6 and 5.7. "Before"
is the standard closure of this table (ca_tables.closure: fewer columns, symbol deletion, derivation, strength-2
product, Roux doubling); "after" adds our families of at most 10,000 columns. A cell (t, v, k), 3 <= t <= 6,
2 <= v <= 25, t <= k <= 10,000, counts when the baseline lists a size there and "after" < "before".
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
DATA, CATOOLS, STATUS, V4 = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
os.makedirs(os.path.join(V4, "data"), exist_ok=True)
os.makedirs(os.path.join(V4, "tables"), exist_ok=True)
LIVE, DOI = "ce719cb", "23839216"
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
    ("roux", r"Martirosyan|Chateauneuf|Cohen-Colbourn-Ling|Roux|doubling|Shokri-Moura"),
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


def shokri_moura():
    """(t, v, k, N, label) of the strength-3 families of Shokri and Moura (2025), from the closed formulas, for every
    prime power 2 <= q <= 25; checked against every entry of Tables 5.6 and 5.7 of Shokri's thesis."""
    out = []
    for q in (2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25):
        D = q * q + q + 1
        out.append((3, q, 2 * D, 4 * q**3 - 5 * q**2 + 2 * q, "Shokri-Moura 2025, Thm 5.2.7 (2-plication)"))
        if q >= 3:
            out.append((3, q, q * D, 5 * q**3 - 6 * q**2 + 2 * q, "Shokri-Moura 2025, Thm 5.2.8 (q-plication)"))
        if q % 2 == 1:
            out.append((3, q, (q + 1) * D, (12 * q**3 - 13 * q**2 + 5 * q - 2) // 2,
                        "Shokri-Moura 2025, Thm 5.2.10 ((q+1)-plication)"))
        out.append((3, q, q * q * D, 8 * q**3 - 10 * q**2 + 4 * q - 1, "Shokri-Moura 2025, Thm 5.2.11 (q^2-plication)"))
        if q % 2 == 0 or q == 3:
            out.append((3, q, q * q * D, 8 * q**3 - 10 * q**2 + 3 * q, "Shokri-Moura 2025, Cor 5.2.12 (q^2-plication)"))
        out.append((3, q, (q * q - q + 1) * D, 8 * q**3 - 10 * q**2 + 3 * q,
                    "Shokri-Moura 2025, Thm 5.2.13 ((q^2-q+1)-plication)"))
    # every "New rows" entry of the thesis' Table 5.6 and the entries of Table 5.7, as (q, k, N)
    table56 = [(2, 14, 16), (2, 21, 30), (2, 28, 30), (3, 26, 69), (3, 39, 87), (3, 91, 135), (3, 117, 135),
               (4, 42, 184), (4, 84, 232), (4, 273, 364), (4, 336, 364), (5, 62, 385), (5, 155, 485), (5, 651, 765),
               (5, 775, 769), (7, 114, 1141), (7, 399, 1435), (7, 2451, 2275), (7, 2793, 2281), (8, 146, 1744),
               (8, 584, 2192), (8, 4161, 3480), (8, 4672, 3480), (9, 182, 2529), (9, 819, 3177), (9, 6643, 5049),
               (9, 7371, 5057), (11, 266, 4741), (11, 1463, 5951), (13, 366, 7969), (13, 2379, 9997), (16, 546, 15136),
               (16, 4368, 18976), (17, 614, 18241), (17, 5219, 22865), (19, 762, 25669), (19, 7239, 32167),
               (23, 1106, 46069), (25, 1302, 59425)]
    table57 = [(3, 52, 110), (5, 186, 599), (7, 456, 1756), (9, 910, 3869), (11, 1596, 7226), (13, 2562, 12115),
               (17, 5526, 27641), (19, 7620, 38854)]
    have = {(v, k, N) for (_, v, k, N, _) in out}
    for q, k, N in table56 + table57:
        assert (q, k, N) in have, (q, k, N)
    return out


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
    sm = shokri_moura()
    for t, v, k, N, lab in sm:
        kk = min(k, T.KMAX)
        b = tab[(t, v)]
        b[: kk + 1] = np.minimum(b[: kk + 1], N)
        entries[(t, v)].append((k, N, lab))
    print(f"Shokri-Moura 2025 bounds added to the baseline: {len(sm)} (all entries of the thesis' Tables 5.6 and 5.7 "
          f"reproduced by the formulas)")
    for (t, v), b in tab.items():
        b[:t] = BIG
    for t in range(2, 7):
        for v in range(2, 26):
            tab[(t, v)]  # every key present
    tab = dict(tab)
    print(f"archival rows used: {sum(len(x) for x in entries.values())} (CITED, snapshots {', '.join(ARCH_SNAPSHOTS)}, "
          f"and Shokri-Moura 2025)")
    before, _ = T.closure(tab)
    import json
    status = json.load(open(STATUS))
    fams = list(csv.DictReader(open(os.path.join(DATA, "families.csv"), newline="")))
    # the 161 families of the paper with at most 10,000 columns; a row for the q = 8 prefix family, if families.csv gains
    # one, is ignored here: that family is added below exactly when its second check has passed
    small_all = [f for f in fams if int(f["k"]) <= 10000 and (f["t"], f["q"], f["n"]) != ("6", "8", "23")]
    assert len(small_all) == 161, len(small_all)
    q8 = status.get("q8_3171", {})
    if q8.get("verdict") == "PASS":
        small_all.append({"t": "6", "q": "8", "n": "23", "k": "3171", "N": str(23 * (8**6 - 8) + 8),
                          "family": "families/CA_6029136_6_3171_8.cphf.txt", "check_log": "record/q8_n23_k4600"})
    pending = {int(q): s_["prefix"] for q, s_ in status.items() if q.isdigit() and s_["verdict"] != "PASS"}
    small = []
    for f in small_all:
        g = dict(f)
        if int(f["t"]) == 6 and int(f["k"]) == 5000 and int(f["q"]) in pending:
            g["k"] = str(pending[int(f["q"])])
            g["cut_from"] = f["k"]
        small.append(g)
    print(f"families counted: {len(small)}; cut to their doubly checked prefixes (second check pending): "
          f"{sorted(pending.items())}; q = 8 prefix family {'included' if q8.get('verdict') == 'PASS' else 'not included (second check ' + q8.get('verdict', 'missing') + ')'}")

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
        famrows.append({"t": t, "q": v, "n": nrows, "k": K, "k_family": int(f.get("cut_from", K)), "N": N, "before_N_at_k": nb,
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

    # cells that rest on our checks alone: drop the families that the table never checked (and the q = 8 prefix family,
    # checked twice but by our programs only); the pending families are already cut to their doubly checked prefixes
    unchecked = {(3, 7, 4, 234), (3, 7, 5, 619), (4, 7, 4, 62), (4, 7, 6, 207), (4, 7, 7, 379), (5, 7, 26, 3000),
                 (5, 9, 16, 6560), (5, 9, 17, 6560), (5, 11, 22, 10000), (6, 19, 15, 1000), (6, 8, 23, 3171)}
    cut2 = [g for g in small if (int(g["t"]), int(g["q"]), int(g["n"]), int(g.get("cut_from", g["k"]))) not in unchecked]
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
    print(f"without the families the table never checked: {lost2 + worse2} cells lost or larger "
          f"({lost2} no longer improved, {worse2} improved by less); by t {dict(sorted(dep2_t.items()))}")
    lost = worse = 0
    dep_t = collections.Counter()

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
    M["aFamCounted"] = str(len(small))
    M["aSM"] = str(len(sm))
    with open(os.path.join(V4, "tables", "v6arch.tex"), "w") as fh:
        fh.write("% written by scripts/v6_archival.py (archival baseline: CITED rows of ca-tools ce719cb, snapshots "
                 "colbourn-2024-11-ug and doi:10.3390/math12121908, and Shokri-Moura 2025; families of the working tree)\n")
        for name, val in M.items():
            fh.write("\\newcommand{\\%s}{%s}\n" % (name, val))
    for name, val in M.items():
        print(f"  macro {name} = {val}")


if __name__ == "__main__":
    main()
