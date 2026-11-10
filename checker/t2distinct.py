"""Second, separately written exact check of an affine strength-2 CPHF in the ca-tools format.
For affine rows a pair of columns is covered by some row exactly when the two columns' tuples of points differ
in some row, so the family is a CPHF exactly when its k column tuples are pairwise distinct. This program reads
the file with its own parser, checks every entry is (1, x) with 0 <= x < q, and counts distinct column tuples with
a hash set; any repeated tuple is a pair of columns no row covers. Exit 0 only on PASS."""
import sys
path, q = sys.argv[1], int(sys.argv[2])
rows = []
with open(path) as fh:
    for line in fh:
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        rows.append([int(x) for x in s.split()])
n = len(rows); k = len(rows[0])
assert all(len(r) == k for r in rows), "ragged rows"
for r, row in enumerate(rows):
    for c, val in enumerate(row):
        if divmod(val, q)[0] != 1 or not (q <= val < 2 * q):
            print(f"NOT AFFINE at row {r} column {c}: {val}\nRESULT FAIL"); sys.exit(1)
seen = {}
dups = 0; first = None
for c, tup in enumerate(zip(*rows)):
    if tup in seen:
        dups += 1
        if first is None:
            first = (seen[tup], c)
    else:
        seen[tup] = c
print(f"{path}: n = {n}, k = {k}, q = {q}, distinct column tuples {len(seen)}, repeats {dups}")
if dups:
    print(f"uncovered pair (equal tuples): {first[0]} {first[1]}\nRESULT FAIL"); sys.exit(1)
print(f"RESULT PASS: SCPHF({n}; {k}, {q}, 2) gives CA({n * (q * q - q) + q}; 2, {k}, {q})")
