"""Recount the improved cells of cells.csv (data repository) for version 2 of the paper, as
papers/covering-arrays-2026/recount_cells.py does (the closure of ca_tables.py in this folder), and settle
the 1,845 strength-3 cells that version 1 held back until Table 5.6 of Shokri's thesis could be read.

Three counts, each: Smolen's table at a commit WITHOUT the rows that cite our release, lowered by the later bounds of
ca_later.tsv, closed under the standard constructions (an array over v symbols serves v - 1, derivation,
the strength-2 product, Roux doubling, fewer columns), against the same closure with our families added; a cell counts
when it improves and the table lists it.

  A  BASE (ec6c172, 2 Nov 2026), as cells.csv was made: must equal cells.csv cell for cell (sizes and previous values);
  B  BASE plus Table 5.6 of the thesis (shokri_thesis_table56.tsv, every size recomputed from the thesis'
     formulas first): which held cells survive;
  C  LIVE (the pinned live commit) plus Table 5.6: the count version 2 states.

    OUT=out python3 recount_v2.py [DATA] [CATOOLS] [LIVE]
Writes OUT/data/recount_v2.txt (the summary) and OUT/data/cells_not_improved_v2.csv (cells of cells.csv that no longer
count in C, if any), and prints the summary.
"""
import csv
import io
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
V2 = os.environ.get("OUT", "out")  # output folder (release copy: was the paper's version folder)
os.makedirs(os.path.join(V2, "data"), exist_ok=True)
DATA = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(HERE))  # this repository
CATOOLS = sys.argv[2] if len(sys.argv) > 2 else "ca-tools"  # a clone of github.com/chrispbsmolen/ca-tools
LIVE = sys.argv[3] if len(sys.argv) > 3 else "ce719cb"
BASE = "ec6c172"
DATA_COMMIT = "ea668c0"
T56 = os.path.join(HERE, "shokri_thesis_table56.tsv")
sys.path.insert(0, HERE)
import numpy as np  # noqa: E402
import ca_tables as T  # noqa: E402

DOI = "23839216"


def show(repo, ref, path):
    return subprocess.run(["git", "-C", repo, "show", f"{ref}:{path}"], check=True, capture_output=True).stdout.decode()


def check_table56():
    """Every size of the transcription equals the thesis' closed formula for its theorem (Section 6.1 of the thesis):
    2-plication     CA(4q^3 - 5q^2 + 2q; 3, 2(q^2+q+1), q)
    q-plication     CA(5q^3 - 6q^2 + 2q; 3, q(q^2+q+1), q)
    q^2-plication   CA(8q^3 - 10q^2 + 4q - 1; 3, q^2(q^2+q+1), q)          (Theorem 5.2.11)
                    CA(8q^3 - 10q^2 + 3q; 3, q^2(q^2+q+1), q), q even or 3  (Corollary 5.2.12)
    (q^2-q+1)-pl.   CA(8q^3 - 10q^2 + 3q; 3, (q^2-q+1)(q^2+q+1), q)        (Theorem 5.2.13)
    except the q = 2, k = 14 line, which Table 5.6 lists as 16 (Sloane's Hadamard array; 2-plication gives 16 too)."""
    n = 0
    for line in open(T56):
        if not line[:1].isdigit():
            continue
        t, q, k, N, src = line.rstrip("\n").split("\t")
        q, k, N = int(q), int(k), int(N)
        m = q * q + q + 1
        if "2-plication" in src and "(q^2" not in src:
            want = (4 * q ** 3 - 5 * q * q + 2 * q, 2 * m)
        elif "(q-plication)" in src:
            want = (5 * q ** 3 - 6 * q * q + 2 * q, q * m)
        elif "Theorem 5.2.11" in src:
            want = (8 * q ** 3 - 10 * q * q + 4 * q - 1, q * q * m)
        elif "Corollary 5.2.12" in src:
            assert q % 2 == 0 or q == 3, line
            want = (8 * q ** 3 - 10 * q * q + 3 * q, q * q * m)
        elif "Theorem 5.2.13" in src:
            want = (8 * q ** 3 - 10 * q * q + 3 * q, (q * q - q + 1) * m)
        else:
            raise AssertionError(line)
        assert (N, k) == want, (line, want)
        n += 1
    return n


def closed_pair(ref, extra):
    rows = [r for r in csv.DictReader(io.StringIO(show(CATOOLS, ref, "table/ca_table.csv"), newline=""))
            if DOI not in r["source_detail"]]
    with tempfile.NamedTemporaryFile("w", suffix=".csv", newline="", delete=False) as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    tab = T.load_later(T.load_catools(f.name))
    os.unlink(f.name)
    for path in extra:
        tab = T.load_later(tab, path)
    base = T.closure(tab)[0]
    trial = {key: b.copy() for key, b in base.items()}
    for r in csv.DictReader(io.StringIO(show(DATA, DATA_COMMIT, "families.csv"), newline="")):
        t, v, K, N = int(r["t"]), int(r["q"]), min(int(r["k"]), T.KMAX), int(r["N"])
        trial[(t, v)][: K + 1] = np.minimum(trial[(t, v)][: K + 1], N)
    after, _ = T.closure(trial)
    out = {}
    for key in sorted(base):
        d = (after[key] < base[key]) & (tab[key] < T.BIG)
        for k in np.nonzero(d)[0]:
            out[(key[0], key[1], int(k))] = (int(after[key][k]), int(base[key][k]))
    return out, base, after


def main():
    n56 = check_table56()
    cells = {}
    held = set()
    for r in csv.DictReader(io.StringIO(show(DATA, DATA_COMMIT, "cells.csv"), newline="")):
        c = (int(r["t"]), int(r["v"]), int(r["k"]))
        cells[c] = (int(r["N"]), int(r["before"]))
        if r["held"].strip():
            held.add(c)
    A = closed_pair(BASE, [])[0]
    assert A == cells, "cells.csv is not the recount against BASE"
    B = closed_pair(BASE, [T56])[0]
    C, C_base, C_after = closed_pair(LIVE, [T56])
    live = subprocess.run(["git", "-C", CATOOLS, "rev-parse", "--short=7", LIVE], check=True, capture_output=True,
                          text=True).stdout.strip()
    lostB = sorted(c for c in cells if c not in B)
    lostC = sorted(c for c in cells if c not in C)
    newC = sorted(c for c in C if c not in cells)
    sizeC = sum(1 for c in cells if c in C and C[c][0] != cells[c][0])
    movedC = sum(1 for c in cells if c in C and C[c][1] != cells[c][1])
    held_lostC = [c for c in lostC if c in held]
    lines = [
        f"data {DATA_COMMIT}; table base {BASE}; live {live}; Table 5.6 lines checked against the thesis formulas: {n56}",
        f"A  base: {len(A)} cells, identical to cells.csv (cells, sizes and previous values): True",
        f"B  base + Table 5.6: {len(B)} cells; cells of cells.csv no longer improved: {len(lostB)} "
        f"(of them held: {sum(1 for c in lostB if c in held)})",
        f"C  live + Table 5.6: {len(C)} cells; cells of cells.csv no longer improved: {len(lostC)} "
        f"(of them held: {len(held_lostC)}); cells not in cells.csv: {len(newC)}; "
        f"cells whose size differs: {sizeC}; previous values lower than in cells.csv: {movedC}",
        f"held cells (v1): {len(held)}; still improved in C: {sum(1 for c in held if c in C)}",
    ]
    by_tv = {}
    for c in lostC:
        by_tv[(c[0], c[1])] = by_tv.get((c[0], c[1]), 0) + 1
    if by_tv:
        lines.append("C  no longer improved, by (t, v): " + ", ".join(f"{t},{v}: {n}" for (t, v), n in sorted(by_tv.items())))
    open(os.path.join(V2, "data", "recount_v2.txt"), "w").write("\n".join(lines) + "\n")
    with open(os.path.join(V2, "data", "cells_not_improved_v2.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["t", "v", "k", "N", "before_v1", "best_known_live_with_table56", "held_v1"])
        for c in lostC:
            w.writerow([c[0], c[1], c[2], cells[c][0], cells[c][1], int(C_base[(c[0], c[1])][c[2]]), int(c in held)])
    print("\n".join(lines))


if __name__ == "__main__":
    main()
