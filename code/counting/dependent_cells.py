"""Cells that rest only on our own full-width check (v3, Major issue 6 and Question 6).

Five strength-6 families with 5,000 columns (q = 9, 11, 13, 16, 17) were checked by the ca-tools program only on a
prefix of their columns (the k of their VERIFIED rows in the table: 3,950, 4,200, 4,400, 4,800 and 4,900). We recount
the improved cells exactly as v2's count C (recount_v2.py: the live table at ce719cb without our rows, lowered by the
later bounds and Table 5.6 of Shokri's thesis, closed under the standard constructions, against the same closure with
our families added) twice: with every family at its full width, and with these five families cut to their verified
prefixes. A cell rests only on our own check if it is improved in the first count and, in the second, either is not
improved or has a larger size.

    python3 dependent_cells.py DATA CATOOLS      (python3 with numpy; imports ca_tables.py from this folder)
"""
import csv
import io
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

CUT = {(6, 9, 5000): 3950, (6, 11, 5000): 4200, (6, 13, 5000): 4400, (6, 16, 5000): 4800, (6, 17, 5000): 4900}


def show(repo, ref, path):
    return subprocess.run(["git", "-C", repo, "show", f"{ref}:{path}"], check=True, capture_output=True).stdout.decode()


def main():
    rows = [r for r in csv.DictReader(io.StringIO(show(CATOOLS, LIVE, "table/ca_table.csv"), newline=""))
            if DOI not in r["source_detail"]]
    # the verified prefixes, read from the table
    pref = {}
    for r in csv.DictReader(io.StringIO(show(CATOOLS, LIVE, "table/ca_table.csv"), newline="")):
        if DOI in r["source_detail"] and r["t"] == "6" and r["tier"] == "VERIFIED":
            pref[(6, int(r["v"]), int(r["N"]))] = int(r["k"])
    with tempfile.NamedTemporaryFile("w", suffix=".csv", newline="", delete=False) as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    tab = T.load_later(T.load_catools(f.name))
    os.unlink(f.name)
    tab = T.load_later(tab, T56)
    base = T.closure(tab)[0]
    fams = list(csv.DictReader(io.StringIO(show(DATA, DATA_COMMIT, "families.csv"), newline="")))

    def after(cut):
        trial = {key: b.copy() for key, b in base.items()}
        for r in fams:
            t, v, K, N = int(r["t"]), int(r["q"]), min(int(r["k"]), T.KMAX), int(r["N"])
            if cut and (t, v, int(r["k"])) in CUT:
                K = CUT[(t, v, int(r["k"]))]
                assert pref[(t, v, N)] == K, (t, v, N, pref.get((t, v, N)))
            trial[(t, v)][: K + 1] = np.minimum(trial[(t, v)][: K + 1], N)
        return T.closure(trial)[0]

    full, capped = after(False), after(True)
    improved, lost, worse, by_t, by_tv = 0, 0, 0, {}, {}
    for key in sorted(base):
        d = (full[key] < base[key]) & (tab[key] < T.BIG)
        for k in np.nonzero(d)[0]:
            improved += 1
            c_imp = capped[key][k] < base[key][k]
            if not c_imp:
                lost += 1
            elif capped[key][k] > full[key][k]:
                worse += 1
            else:
                continue
            by_t[key[0]] = by_t.get(key[0], 0) + 1
            by_tv[key] = by_tv.get(key, 0) + 1
    print(f"improved cells (count C): {improved}")
    print(f"resting only on our own full-width check: {lost + worse} (no longer improved with the five families cut to "
          f"their verified prefixes: {lost}; still improved but with a larger size: {worse})")
    print("by t:", dict(sorted(by_t.items())))
    print("by (t, v):", ", ".join(f"({t},{v}): {n}" for (t, v), n in sorted(by_tv.items())))


if __name__ == "__main__":
    main()
