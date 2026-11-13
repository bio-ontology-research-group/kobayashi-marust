"""Differential test of the Lean OFN parser (km-owl-parse) against the Rust
parser (engine example ofn_dump) on the survey inputs.

usage: differential.py INPUTS.tsv OUTDIR LEAN_EXE RUST_EXE [--only-f] [--limit N]

INPUTS.tsv comes from classify.py (path, size, inF, p2_status). For every
input, runs both tools one after the other under `nice` and `timeout 300`,
with two inputs in flight at most (so at most two processes run at once),
and appends one JSON line per input to OUTDIR/results.jsonl. Inputs already
in results.jsonl are skipped, so the run can be resumed.
"""
import csv, json, os, subprocess, sys, threading, queue, time

def run(cmd):
    t0 = time.monotonic()
    p = subprocess.run(["nice", "timeout", "300", "/usr/bin/time", "-f", "MAXRSS %M"] + cmd,
                       capture_output=True, text=True, errors="replace")
    wall = time.monotonic() - t0
    rss = None
    err_lines = []
    for line in p.stderr.splitlines():
        if line.startswith("MAXRSS "):
            rss = int(line.split()[1])
        else:
            err_lines.append(line)
    try:
        out = json.loads(p.stdout.strip().splitlines()[-1]) if p.stdout.strip() else None
    except Exception:
        out = None
    if out is None:
        out = {"status": "crash", "reason": f"exit {p.returncode}: " + " | ".join(err_lines[-3:])}
    return out, wall, rss, err_lines, p.returncode

def compare(lean, rust):
    """Differences between the Lean and Rust dumps of one accepted input."""
    diffs = []
    for key in ("classes", "objectProperties"):
        l, r = set(lean.get(key, [])), set(rust.get(key, []))
        if l != r:
            diffs.append({"field": key, "leanOnly": sorted(l - r)[:20], "rustOnly": sorted(r - l)[:20],
                          "leanOnlyCount": len(l - r), "rustOnlyCount": len(r - l)})
    lc, rc = lean.get("axiomCounts", {}), rust.get("axiomCounts", {})
    for k in sorted(set(lc) | set(rc)):
        if lc.get(k, 0) != rc.get(k, 0):
            diffs.append({"field": "axiomCounts." + k, "lean": lc.get(k, 0), "rust": rc.get(k, 0)})
    return diffs

def main():
    inputs, outdir, lean_exe, rust_exe = sys.argv[1:5]
    only_f = "--only-f" in sys.argv
    limit = int(sys.argv[sys.argv.index("--limit") + 1]) if "--limit" in sys.argv else None
    os.makedirs(outdir, exist_ok=True)
    res_path = os.path.join(outdir, "results.jsonl")
    done = set()
    if os.path.exists(res_path):
        for line in open(res_path):
            done.add(json.loads(line)["path"])
    rows = [r for r in csv.DictReader(open(inputs), delimiter="\t")
            if (not only_f or r["inF"] == "1") and r["path"] not in done]
    if limit:
        rows = rows[:limit]
    q = queue.Queue()
    for r in rows:
        q.put(r)
    lock = threading.Lock()
    out = open(res_path, "a")

    def worker():
        while True:
            try:
                r = q.get_nowait()
            except queue.Empty:
                return
            lean, lwall, lrss, lerr, _ = run([lean_exe, r["path"]])
            rust, rwall, rrss, _, _ = run([rust_exe, r["path"]])
            rec = {"path": r["path"], "size": int(r["size"]), "inF": r["inF"] == "1",
                   "lean": {"status": lean["status"], "reason": lean.get("reason"), "wall": round(lwall, 3),
                            "maxrssKiB": lrss, "times": " ".join(lerr)},
                   "rust": {"status": rust["status"], "reason": rust.get("reason"), "wall": round(rwall, 3),
                            "maxrssKiB": rrss, "extra": rust.get("rust")},
                   "classes": len(lean.get("classes", [])), "objectProperties": len(lean.get("objectProperties", [])),
                   "axiomCounts": lean.get("axiomCounts")}
            if lean["status"] == "ok" and rust["status"] == "ok":
                rec["diffs"] = compare(lean, rust)
            with lock:
                out.write(json.dumps(rec) + "\n")
                out.flush()
                print(f'{rec["lean"]["status"]:8} {rec["rust"]["status"]:8} diffs={len(rec.get("diffs", []))} '
                      f'{lwall:7.2f}s {r["path"]}', flush=True)

    threads = [threading.Thread(target=worker) for _ in range(2)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

if __name__ == "__main__":
    main()
