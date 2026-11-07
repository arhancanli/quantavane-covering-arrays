"""Which constructions held the previous values of the improved cells (v2, Section 7, Table "prior").

    python3 -E prior_methods.py [DATA] [CATOOLS]

cells.csv (data repository, commit ea668c0) gives, for every improved cell (t, v, k), the value the table listed
("table": Smolen's table at ec6c172 without our rows, lowered by the later bounds of ca_later.tsv, before
any construction is applied) and the best value before ("before", after the standard constructions). For each cell this
script finds the entry that gives the "table" value: a counted row of the table (CITED or VERIFIED, t, v equal, at
least k columns, N equal), or a line of ca_later.tsv; when several do, the one with the fewest columns. Its construction
label (the table's "construction" field, which for the November 2024 rows is Colbourn's own method label; for a later
bound its source) is reduced by removing trailing " fuse" and " postop ..." (symbol fusion and post-optimization) and
sorted into kinds by the keyword rules in KINDS. Writes OUT/prior.tex and OUT/data/prior_labels.csv (every label with its
kind and counts) and prints both.
"""
import collections
import csv
import io
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(HERE))  # this repository
CATOOLS = sys.argv[2] if len(sys.argv) > 2 else "ca-tools"  # a clone of github.com/chrispbsmolen/ca-tools
LATER = os.path.join(HERE, "ca_later.tsv")
BASE, DATA_COMMIT, DOI = "ec6c172", "ea668c0", "23839216"
V2 = os.environ.get("OUT", "out")  # output folder (release copy: was the paper's version folder)
os.makedirs(os.path.join(V2, "data"), exist_ok=True)

KINDS = [  # (kind, regular expression on the reduced label), first match wins
    ("later", r"^LATER: "),
    ("cphf", r"CPHF|SCPHF|covering perfect hash"),
    ("phf", r"^perfect hash family"),
    ("power", r"^Power (N-)?CT"),
    ("roux", r"Martirosyan|Chateauneuf|Cohen-Colbourn-Ling|Roux|doubling"),
    ("add", r"^Add (a|\d+) factors?|Derive|Power CZ|product|Product"),
    ("oa", r"orthogonal array|Augment OA|extended OA|OA\b"),
    ("cyclic", r"[Cc]yclotomy|[Cc]yclic"),
    ("search", r"IPOG|annealing|Annealing|tabu|Tabu|Torres Jimenez|Dwyer|greedy|Greedy|search|Search"),
]
KIND_TEXT = {"later": "bounds published after November 2024",
             "cphf": "CPHFs found by computer",
             "phf": "``perfect hash family'' (Colbourn's label)",
             "power": "power construction of Colbourn and Torres-Jimenez",
             "roux": "Roux-type and related recursions",
             "add": "adding factors",
             "oa": "orthogonal arrays and their extensions",
             "cyclic": "cyclotomy",
             "search": "other computer searches",
             "other": "other"}


def show(repo, ref, path):
    return subprocess.run(["git", "-C", repo, "show", f"{ref}:{path}"], check=True, capture_output=True).stdout.decode()


def reduce(label):
    return re.sub(r"(\s+fuse|\s+postop.*)+$", "", label.strip())


def kind(label):
    for k, rx in KINDS:
        if re.search(rx, label):
            return k
    return "other"


def tex(x):
    return f"{int(x):,}".replace(",", "{,}")


def main():
    entries = collections.defaultdict(list)  # (t, v) -> [(k, N, label)]
    for r in csv.DictReader(io.StringIO(show(CATOOLS, BASE, "table/ca_table.csv"), newline="")):
        if DOI in r["source_detail"] or r["tier"] not in ("CITED", "VERIFIED"):
            continue
        entries[(int(r["t"]), int(r["v"]))].append((int(float(r["k"])), int(float(r["N"])),
                                                    reduce(r["construction"] or r["source_detail"])))
    for line in open(LATER):
        if not line[:1].isdigit():
            continue
        t, v, k, N, src = line.rstrip("\n").split("\t")[:5]
        entries[(int(t), int(v))].append((int(k), int(N), "LATER: " + src.split(",")[0].split(" (")[0]))
    cells = list(csv.DictReader(io.StringIO(show(DATA, DATA_COMMIT, "cells.csv"), newline="")))
    by_kind, by_kind_direct, by_label = collections.Counter(), collections.Counter(), collections.Counter()
    saving = collections.defaultdict(list)
    for c in cells:
        t, v, k, table, N = int(c["t"]), int(c["v"]), int(c["k"]), int(c["table"]), int(c["N"])
        cands = [e for e in entries[(t, v)] if e[0] >= k and e[1] == table]
        assert cands, c
        e = min(cands, key=lambda e: (e[0], e[2]))
        kd = kind(e[2])
        by_kind[kd] += 1
        by_label[(kd, e[2])] += 1
        if c["how"].startswith("direct"):
            by_kind_direct[kd] += 1
        saving[kd].append((int(c["before"]) - N) / int(c["before"]))
    total = len(cells)
    order = ["cphf", "phf", "power", "roux", "add", "oa", "cyclic", "search", "later", "other"]
    L = [r"\begin{tabular}{lrrr}", r"\toprule",
         r"previous value from & cells & of them direct & median saving \\", r"\midrule"]
    for kd in order:
        if by_kind[kd]:
            s = sorted(saving[kd])
            L.append(f"{KIND_TEXT[kd]} & {tex(by_kind[kd])} & {tex(by_kind_direct[kd])} & "
                     f"{100 * s[len(s) // 2]:.1f}\\% \\\\")
    L += [r"\midrule", f"total & {tex(total)} & {tex(sum(by_kind_direct.values()))} & \\\\", r"\bottomrule",
          r"\end{tabular}"]
    open(os.path.join(V2, "prior.tex"), "w").write("\n".join(L) + "\n")
    with open(os.path.join(V2, "data", "prior_labels.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["kind", "label", "cells"])
        for (kd, lab), n in sorted(by_label.items(), key=lambda x: -x[1]):
            w.writerow([kd, lab, n])
    with open(os.path.join(V2, "prior_macros.tex"), "w") as fh:
        fh.write("%% written by scripts/prior_methods.py\n")
        for kd in order:
            name = "pr" + {"cphf": "Cphf", "phf": "Phf", "power": "Power", "roux": "Roux", "add": "Add", "oa": "Oa", "cyclic": "Cyc",
                           "search": "Search", "later": "Later", "other": "Other"}[kd]
            fh.write("\\newcommand{\\%s}{%s}\n" % (name, tex(by_kind[kd])))
        allsav = sorted(x for kd in saving for x in saving[kd])
        fh.write("\\newcommand{\\prMedianSaving}{%.1f\\%%}\n" % (100 * allsav[len(allsav) // 2]))
    print("\n".join(L))
    for (kd, lab), n in sorted(by_label.items(), key=lambda x: -x[1])[:40]:
        print(f"{n:7d}  {kd:9s}  {lab[:100]}")
    print("labels:", len(by_label), " kinds:", dict(by_kind))


if __name__ == "__main__":
    main()
