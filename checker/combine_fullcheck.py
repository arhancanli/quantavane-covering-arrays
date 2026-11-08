"""Combine the outputs of the Kaggle full-check sessions.

    python3 -I combine_fullcheck.py dataset/plan.json OUTPUT_DIR [OUTPUT_DIR ...]

Reads every results_*.jsonl under the output directories (downloaded with `kaggle kernels output <id> -p DIR`) and
judges each family under each of its two plans (records of the plan's mode only):
- full width: PASS when, for the family's file and checker hashes, each of its chunks has a record with status "done"
  (duplicates must agree), the chunks' x1 ranges are those of plan.json, the step counts add up to
  C(k-1, 4) - C(k-3, 2) (every 4-set {x1, x2, x, y} after column 0 with at least one further column between x2 and y),
  every chunk certified all n rows as affine progressions, and no chunk found an uncovered base set;
- tail: the same for the tail chunks, whose steps must add up to the plan's tail_steps_beyond_prefix (the base sets
  whose largest column is at least the table's prefix L). With the table's check of the first L columns (its
  certificate is exactly our prefix) and shift invariance (certified for every row), a tail PASS decides every 6-set.
A plan FAILS when any of its chunks found an uncovered base set (the sets are printed) and is INCOMPLETE otherwise.
The exit code is 0 when every family passes under at least one plan and none fails.
"""
import glob
import json
import math
import os
import sys


def judge(fam, plan, recs, mode):
    chunks = fam["tail_chunks"] if mode == "tail" else fam["chunks"]
    want_tail = fam["table_prefix"] if mode == "tail" else 0
    expected = fam["tail_steps_beyond_prefix"] if mode == "tail" else math.comb(fam["k"] - 1, 4) - math.comb(fam["k"] - 3, 2)
    by = {}
    for r in recs:
        if (r["family_sha256"] == fam["sha256"] and r["checker_sha256"] == plan["checker_sha256"]
                and r.get("mode", "full") == mode and r.get("tail", 0) == want_tail and r["status"] == "done"):
            by.setdefault(r["chunk"], []).append(r)
    problems, unc_sets, total_steps, secs = [], [], 0, 0.0
    for ch in chunks:
        rs = by.get(ch["id"], [])
        if not rs:
            problems.append(f"chunk {ch['id']} missing")
            continue
        for r in rs:
            res = r["result"]
            if (r["x1_from"], r["x1_to"]) != (ch["x1_from"], ch["x1_to"]) or res["steps"] != ch["steps"]:
                problems.append(f"chunk {ch['id']}: range or steps differ from the plan")
            if res.get("tail", 0) != want_tail:
                problems.append(f"chunk {ch['id']}: run with another L")
            if r["progressions"]["rows_certified"] != fam["n"]:
                problems.append(f"chunk {ch['id']}: not every row certified")
            if res["uncovered_base_sets"]:
                unc_sets += res["first_sets"]
        if len({json.dumps(r["result"]["uncovered_base_sets"]) for r in rs}) > 1:
            problems.append(f"chunk {ch['id']}: duplicate records disagree")
        total_steps += rs[0]["result"]["steps"]
        secs += rs[0]["seconds"]
    if unc_sets:
        v = "FAIL"
    elif problems or total_steps != expected:
        v = "INCOMPLETE"
    else:
        v = "PASS"
    line = (f"{mode:4s}: {v}; {len(by)} of {len(chunks)} chunks, {total_steps:,} of {expected:,} steps, "
            f"{secs / 3600:.1f} session-hours" + (f"; problems: {problems[:5]}" if problems else "")
            + (f"; uncovered base sets: {unc_sets[:10]}" if unc_sets else ""))
    return v, line


def main():
    plan = json.load(open(sys.argv[1]))
    recs = []
    for d in sys.argv[2:]:
        for path in glob.glob(os.path.join(d, "**", "results_*.jsonl"), recursive=True):
            for ln in open(path):
                if ln.strip():
                    recs.append(json.loads(ln))
    ok = True
    for fam in plan["families"]:
        vf, lf = judge(fam, plan, recs, "full")
        vt, lt = judge(fam, plan, recs, "tail")
        print(f"q {fam['q']} ({fam['file']}, sha256 {fam['sha256'][:16]}..., table prefix {fam['table_prefix']}):")
        print(f"  {lf}")
        print(f"  {lt}")
        if "FAIL" in (vf, vt) or "PASS" not in (vf, vt):
            ok = False
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
