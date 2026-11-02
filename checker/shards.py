"""Plans the exact check of one family in shards for .github/workflows/verify.yml: contiguous ranges of x1 (the
checkers' outer task, CHECK_TASKS=a:b) with about equal work, the work of x1 taken as (k - x1)^(t - 3).
    python3 checker/shards.py FAMILY T SHARDS   ->   matrix={"include": [{"i": 0, "tasks": "1:57"}, ...]}"""
import json, sys
path, t, m = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
first = open(path).readline().split()
k = int(first[2]) if first[:2] == ["best", "k"] else len(next(l for l in open(path) if l.strip() and not l.startswith(("#", "best"))).split())
last = k - (t - 1)                  # x1 runs 1..k-5 at strength 6, 1..k-4 at strength 5
w = [(k - x) ** (t - 3) for x in range(1, last + 1)]
total, inc, a, acc = sum(w), [], 1, 0
for x in range(1, last + 1):
    acc += w[x - 1]
    if acc >= total * (len(inc) + 1) / m or x == last:
        inc.append({"i": len(inc), "tasks": f"{a}:{x}"}); a = x + 1
print("matrix=" + json.dumps({"include": inc}))
