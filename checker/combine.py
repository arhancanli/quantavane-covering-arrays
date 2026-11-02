"""Combines the shards of .github/workflows/verify.yml: every shard must have finished (its PARTIAL line), the ranges
must cover x1 = 1..K exactly once, and no shard may report a set of columns on one hyperplane in every row or a random
set missing a tuple. Prints PASS or FAIL with the counts; exits 1 on FAIL.
    python3 checker/combine.py SHARD_DIR"""
import glob, re, sys
cover, bad, missing, K, n = [], 0, 0, None, 0
for f in sorted(glob.glob(sys.argv[1] + "/**/out.txt", recursive=True)):
    s = open(f).read(); n += 1
    p = re.search(r"PARTIAL: tasks x1 = (\d+)\.\.(\d+) of 1\.\.(\d+)", s)
    if not p:
        print(f"FAIL: {f} has no PARTIAL line (the shard did not finish)"); sys.exit(1)
    cover.append((int(p.group(1)), int(p.group(2)))); K = int(p.group(3))
    h = re.search(r"(\d+) always on one hyperplane", s)
    bad += int(h.group(1)) if h else 0
    mm = re.search(r"(\d+) missing a tuple", s)
    missing += int(mm.group(1)) if mm else 0
cover.sort()
contiguous = cover and cover[0][0] == 1 and cover[-1][1] == K and all(b + 1 == c for (_, b), (c, _) in zip(cover, cover[1:]))
ok = contiguous and bad == 0 and missing == 0
print(f"{n} shards, x1 = 1..{K} {'covered once' if contiguous else 'NOT covered exactly once'}; "
      f"{bad} base sets on one hyperplane in every row; {missing} random sets missing a tuple")
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
