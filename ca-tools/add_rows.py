#!/usr/bin/env python3
"""add_rows.py - appends the covering array sizes of Canli 2026 (Table 2 of the paper: 279 sizes from 143 Sherwood
covering perfect hash families, t = 3 to 6, v = 4 to 25, k up to 10,000) to table/ca_table.csv of
github.com/chrispbsmolen/ca-tools as CITED S7 rows, the way tools/add_tjim7.py enters the sizes of Torres-Jimenez and
Izquierdo-Marquez 2024. Usage, from the ca-tools repository root:
    python3 add_rows.py rows.csv ID YYYY-MM-DD
ID is the paper's DOI (doi:10.5281/zenodo.N) or arXiv id (arXiv:YYMM.NNNNN). rows.csv is ca-tools/rows.csv of
github.com/arhancanli/quantavane-covering-arrays: one row per size (t, v, k, N; it improves k_from to k), the family
it comes from (families/<family>.cphf.txt there: family_n rows, family_k columns, family_N runs, strength family_t,
family_q symbols) and the constructions applied after it (steps). Each row's best known value is recomputed here from
the table's CITED and VERIFIED rows; a row that no longer improves on it is left out and listed."""
import csv, io, sys, datetime
SRC, ID, DATE = sys.argv[1], sys.argv[2], sys.argv[3]
datetime.datetime.strptime(DATE, "%Y-%m-%d")
assert ID.startswith(("doi:", "arXiv:")), "ID must be doi:... or arXiv:..."
REPO = "https://github.com/arhancanli/quantavane-covering-arrays"
TITLE = "New upper bounds for covering array numbers from partly cyclic covering perfect hash families"
raw = open("table/ca_table.csv", "rb").read().decode("utf-8")
lines = raw.split("\r\n"); assert lines[-1] == ""
rows = list(csv.reader(lines[:-1]))
hdr = rows[0]; assert hdr[:5] == ["t", "v", "k", "N", "tier"] and hdr[7] == "snapshot_id"
if any(r[7] == ID for r in rows[1:]):
    sys.exit("these rows are already in the table")
best = {}
for r in rows[1:]:
    if r[4] in ("CITED", "VERIFIED"):
        best.setdefault((int(r[0]), int(r[1])), []).append((int(float(r[2])), int(float(r[3])), r[5], r[6]))
def known(t, v, k):
    c = [(n, -kk, sid, det) for kk, n, sid, det in best.get((t, v), []) if kk >= k]
    return min(c) if c else None
def explain(step):
    if step.startswith("symbols"):
        return step + " (an array over v + 1 symbols serves v symbols)"
    if step.startswith("derive"):
        return step + " (derivation: CAN(t - 1, k - 1, v) <= CAN(t, k, v) / v)"
    return step + " (Roux-type doubling for strength 3, Chateauneuf and Kreher)"
new, left = [], []
for i, d in enumerate(csv.DictReader(open(SRC, newline="")), 1):
    t, v, k, N = int(d["t"]), int(d["v"]), int(d["k"]), int(d["N"])
    kb = known(t, v, k)
    if kb is not None and N >= kb[0]:
        left.append((i, t, v, k, N, kb[0]))
        continue
    ft, fq = int(d["family_t"]), int(d["family_q"])
    fam = "SCPHF(%s; %s, %d^%d, %d)" % (d["family_n"], d["family_k"], fq, ft - 1, ft)
    then = "" if d["steps"] == "direct" else "; then " + "; ".join(explain(s) for s in d["steps"].split("; "))
    prev = ("previous best %d at this k (%s %s)" % (kb[0], kb[2], kb[3])) if kb else "no previous value"
    held = ("; part of this range is not yet compared with Table 5.6 of M. Shokri's thesis (Ottawa, 2026)"
            if d["held"] else "")
    notes = ("credit: Arhan Canli 2026 (%s, Table 2 row %d); exceeds table: %s; improves k = %s to %d; the family is "
             "families/%s.cphf.txt and the output of the exact check written separately from the search is "
             "checks/%s.*, in %s%s" % (ID, i, prev, d["k_from"], k, d["family"], d["family"], REPO, held))
    new.append([t, v, k, N, "CITED", "S7",
                "Canli 2026, %s, Table 2 row %d, from %s, %s" % (TITLE, i, fam, d["family"]),
                ID, "", "", DATE, notes, "", "",
                "Sherwood covering perfect hash family %s over AG(%d, %d), found by the author's search (rows that are "
                "affine progressions of an invertible affine map, plus random rows), converted to a covering array "
                "CA(%s; %d, %s, %d) of n(q^t - q) + q rows (Sherwood, Martirosyan and Colbourn 2006)%s"
                % (fam, ft - 1, fq, d["family_N"], ft, d["family_k"], fq, then)])
b = io.StringIO(); w = csv.writer(b, lineterminator="\r\n")
for r in new: w.writerow(r)
open("table/ca_table.csv", "wb").write((raw + b.getvalue()).encode("utf-8"))
print("%d CITED S7 rows added; date %s; id %s" % (len(new), DATE, ID))
for i, t, v, k, N, kb in left:
    print("left out, row %d: CA(%d; %d, %d, %d) no longer beats the table's %d" % (i, N, t, k, v, kb))
