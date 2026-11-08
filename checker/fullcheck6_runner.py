# Full-width exact check of one strength-6 family of the Quantavane covering-array paper (version 4), on a Kaggle CPU
# session: fullcheck6.c, a second program written separately from the search and from the data repository's checkers.
# This kernel runs the chunks ASSIGN_CHUNKS (ranges of the second column x1 of the base sets) of the family with
# q = ASSIGN_Q, in mode ASSIGN_MODE: "full" (every base set) or "tail" (only the base sets whose largest column is at
# least the prefix that the ca-tools table checked). It skips chunks already done (results_*.jsonl found under
# /kaggle/input with the same file and checker hashes and the same mode), stops starting chunks after BUDGET_HOURS, and
# writes one JSON line per finished chunk to /kaggle/working/results_<slug>.jsonl. combine_fullcheck.py (in the package)
# accepts a family only when every chunk of a plan ran, with the expected step count and no uncovered base set.
import glob
import hashlib
import json
import os
import platform
import subprocess
import time

ASSIGN_Q = None
ASSIGN_CHUNKS = None
ASSIGN_MODE = None
KERNEL_SLUG = None
BUDGET_HOURS = 11.5
T0 = time.time()
ROOT = os.environ.get("FC_KAGGLE_ROOT", "/kaggle")  # override only for a local test of this script
W = os.path.join(ROOT, "working")


def utc():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def log(msg):
    line = f"[{utc()} +{(time.time() - T0) / 3600:.2f} h] {msg}"
    print(line, flush=True)
    with open(os.path.join(W, f"log_{KERNEL_SLUG}.txt"), "a") as f:
        f.write(line + "\n")


plans = glob.glob(os.path.join(ROOT, "input", "**", "plan.json"), recursive=True)
assert plans, "dataset with plan.json not found under /kaggle/input"
DS = os.path.dirname(plans[0])
plan = json.load(open(plans[0]))
fam = next(f for f in plan["families"] if f["q"] == ASSIGN_Q)
assert ASSIGN_MODE in ("full", "tail")
TAIL = fam["table_prefix"] if ASSIGN_MODE == "tail" else 0  # fullcheck6's L: only base sets with largest column >= L
CHUNKLIST = fam["tail_chunks"] if ASSIGN_MODE == "tail" else fam["chunks"]
FILE = os.path.join(DS, fam["file"])
SRC = os.path.join(DS, plan["checker"])
assert sha256(FILE) == fam["sha256"], "family file hash differs from plan.json"
assert sha256(SRC) == plan["checker_sha256"], "checker hash differs from plan.json"
cpu_model = ""
try:
    cpu_model = next((ln.split(":", 1)[1].strip() for ln in open("/proc/cpuinfo") if ln.startswith("model name")), "")
except OSError:
    pass
NCPU = int(os.environ.get("FC_THREADS", os.cpu_count() or 1))
log(f"kernel {KERNEL_SLUG}: q {ASSIGN_Q}, mode {ASSIGN_MODE} (L = {TAIL}), chunks {ASSIGN_CHUNKS}; dataset {DS}; {NCPU} CPUs "
    f"({cpu_model}); {platform.platform()}")

# chunks already done in earlier sessions (outputs of earlier kernels attached as inputs)
done = {}
for path in glob.glob(os.path.join(ROOT, "input", "**", "results_*.jsonl"), recursive=True):
    for ln in open(path):
        try:
            r = json.loads(ln)
        except ValueError:
            continue
        if (r.get("family_sha256") == fam["sha256"] and r.get("checker_sha256") == plan["checker_sha256"]
                and r.get("status") == "done" and r.get("mode", "full") == ASSIGN_MODE and r.get("tail", 0) == TAIL):
            done[r["chunk"]] = path
if done:
    log(f"chunks done earlier, skipped: {sorted(done)}")

BIN = os.path.join(W, "fullcheck6")
cc = "gcc" if subprocess.run(["which", "gcc"], capture_output=True).returncode == 0 else "cc"
subprocess.run([cc, "-O3", "-march=native", "-o", BIN, SRC, "-lpthread"], check=True)
log(subprocess.run([cc, "--version"], capture_output=True, text=True).stdout.splitlines()[0])

# self-tests: random families (brute force, signature table and Algorithm R must agree), and a subarray of the family
for seed in (1, 2):
    r = subprocess.run([BIN, str(ASSIGN_Q), "-", "selftest", str(seed)], capture_output=True, text=True)
    last = r.stderr.strip().splitlines()[-1] if r.stderr.strip() else ""
    log(f"selftest seed {seed}: {last}")
    assert r.returncode == 0 and "agree (" in last, "self-test failed"
b = subprocess.run([BIN, str(ASSIGN_Q), FILE, "brute", "34", "3"], capture_output=True, text=True)
f = subprocess.run([BIN, str(ASSIGN_Q), FILE, "fastlist", "34", "3"], capture_output=True, text=True)
assert b.returncode == 0 and f.returncode == 0 and b.stdout == f.stdout, "brute force and fast method differ on a subarray"
log(f"subarray (first 34 columns, first 3 rows): {b.stderr.strip()} | {f.stderr.strip()}; lists identical")

out = os.path.join(W, f"results_{KERNEL_SLUG}.jsonl")
chunks = {c["id"]: c for c in CHUNKLIST}
rate = fam["est_rate"]  # steps per second, replaced by the measured rate after the first chunk
measured_steps, measured_secs = 0, 0.0
todo = [c for c in ASSIGN_CHUNKS if c not in done]
for cid in todo:
    ch = chunks[cid]
    left = BUDGET_HOURS * 3600 - (time.time() - T0)
    need = ch["steps"] / rate
    if need > left:
        log(f"stop: chunk {cid} needs about {need / 3600:.2f} h, {left / 3600:.2f} h left")
        break
    t = time.time()
    start = utc()
    try:
        r = subprocess.run([BIN, str(ASSIGN_Q), FILE, "check", str(ch["x1_from"]), str(ch["x1_to"]), str(NCPU), str(TAIL)],
                           capture_output=True, text=True, timeout=max(60, left))
    except subprocess.TimeoutExpired:
        log(f"chunk {cid} hit the time budget; not recorded")
        break
    secs = time.time() - t
    res = next((json.loads(ln.split("RESULT ", 1)[1]) for ln in r.stdout.splitlines() if ln.startswith("RESULT ")), None)
    prog = next((json.loads(ln.split("PROGRESSIONS ", 1)[1]) for ln in r.stdout.splitlines() if ln.startswith("PROGRESSIONS ")), None)
    ok = (res is not None and r.returncode in (0, 1) and res["steps"] == res["expected_steps"] == ch["steps"]
          and res.get("tail", 0) == TAIL and res["internal_disagreements"] == 0 and prog is not None
          and prog["rows_certified"] == fam["n"])
    rec = {"chunk": cid, "mode": ASSIGN_MODE, "tail": TAIL, "q": ASSIGN_Q, "file": fam["file"], "family_sha256": fam["sha256"],
           "checker_sha256": plan["checker_sha256"], "x1_from": ch["x1_from"], "x1_to": ch["x1_to"],
           "status": "done" if ok else "error", "exit_code": r.returncode, "start_utc": start, "end_utc": utc(),
           "seconds": round(secs, 1), "cpus": NCPU, "cpu_model": cpu_model, "kernel": KERNEL_SLUG,
           "progressions": prog, "result": res, "stderr_tail": r.stderr[-2000:]}
    with open(out, "a") as fo:
        fo.write(json.dumps(rec) + "\n")
    if res is not None:
        measured_steps += res["steps"]
        measured_secs += secs
        rate = measured_steps / max(measured_secs, 1.0)
    log(f"chunk {cid} (x1 {ch['x1_from']}..{ch['x1_to'] - 1}): {'done' if ok else 'ERROR'}, exit {r.returncode}, "
        f"{res['uncovered_base_sets'] if res else '?'} uncovered base sets, {secs / 3600:.2f} h, {rate:.3g} steps/s")
    if res and res["uncovered_base_sets"]:
        log(f"UNCOVERED BASE SETS: {res['first_sets']}")

recs = [json.loads(ln) for ln in open(out)] if os.path.exists(out) else []
finished = sorted(set(done) | {x["chunk"] for x in recs if x["status"] == "done"})
remaining = [c for c in ASSIGN_CHUNKS if c not in finished]
unc = sum(x["result"]["uncovered_base_sets"] for x in recs if x.get("result"))
summary = {"kernel": KERNEL_SLUG, "q": ASSIGN_Q, "mode": ASSIGN_MODE, "tail": TAIL, "assigned": ASSIGN_CHUNKS, "finished": finished, "remaining": remaining,
           "uncovered_base_sets_this_session": unc, "hours": round((time.time() - T0) / 3600, 2)}
json.dump(summary, open(os.path.join(W, f"summary_{KERNEL_SLUG}.json"), "w"), indent=1)
log(f"summary: {summary}")
