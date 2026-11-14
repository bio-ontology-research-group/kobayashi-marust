"""v1.7.0 C0 differential test of the Lean OFN parser (km-owl-parse) against
the Rust parser (the v1.6.2 `ofn_dump` example) and an independent head
count (heads.py), on survey inputs outside the v1.6.2 fragment F.

usage: differential.py INPUTS.tsv OUTDIR LEAN_EXE RUST_EXE [--limit N] [--ore-only | --non-ore] [--max-size BYTES]

Per input: the Lean and Rust dumps run one after the other under `nice` and
`timeout 300`, two inputs in flight. Recorded: accept/reject of both, the
class and object-property name sets (Lean vs Rust), the 12 axiom counts the
Rust dump reports, and every Lean axiom count against heads.py. Resumable.
"""
import csv, json, os, subprocess, sys, threading, queue, time

HERE = os.path.dirname(os.path.abspath(__file__))
SHARED = ["subClassOf", "equivalentClasses", "disjointClasses", "domain", "range",
          "subObjectPropertyOf", "equivalentObjectProperties", "inverseObjectProperties",
          "transitive", "symmetric", "declareClass", "declareObjectProperty"]

def run(cmd):
    t0 = time.monotonic()
    p = subprocess.run(["nice", "timeout", "300"] + cmd, capture_output=True, text=True, errors="replace")
    wall = time.monotonic() - t0
    try:
        out = json.loads(p.stdout.strip().splitlines()[-1]) if p.stdout.strip() else None
    except Exception:
        out = None
    if out is None:
        out = {"status": "crash", "reason": f"exit {p.returncode}: " + " | ".join(p.stderr.splitlines()[-3:])}
    return out, wall

def compare(lean, rust, heads):
    diffs = []
    for key in ("classes", "objectProperties"):
        l, r = set(lean.get(key, [])), set(rust.get(key, []))
        if l != r:
            diffs.append({"field": key, "leanOnly": sorted(l - r)[:10], "rustOnly": sorted(r - l)[:10],
                          "leanOnlyCount": len(l - r), "rustOnlyCount": len(r - l)})
    lc, rc = lean.get("axiomCounts", {}), rust.get("axiomCounts", {})
    for k in SHARED:
        if lc.get(k, 0) != rc.get(k, 0):
            diffs.append({"field": "rustCounts." + k, "lean": lc.get(k, 0), "rust": rc.get(k, 0)})
    if heads is not None:
        for k in sorted(set(lc) | set(heads)):
            if lc.get(k, 0) != heads.get(k, 0):
                diffs.append({"field": "headCounts." + k, "lean": lc.get(k, 0), "heads": heads.get(k, 0)})
    return diffs

def main():
    inputs, outdir, lean_exe, rust_exe = sys.argv[1:5]
    limit = int(sys.argv[sys.argv.index("--limit") + 1]) if "--limit" in sys.argv else None
    max_size = int(sys.argv[sys.argv.index("--max-size") + 1]) if "--max-size" in sys.argv else None
    ore_only = "--ore-only" in sys.argv
    os.makedirs(outdir, exist_ok=True)
    res_path = os.path.join(outdir, "results.jsonl")
    done = set()
    if os.path.exists(res_path):
        for line in open(res_path):
            done.add(json.loads(line)["path"])
    rows = [r for r in csv.DictReader(open(inputs), delimiter="\t")
            if r["inF"] == "0" and r["path"] not in done and not r["path"].endswith(".ttl")
            and (not ore_only or "ore_ont_" in r["path"])
            and (not ("--non-ore" in sys.argv) or "ore_ont_" not in r["path"])
            and (max_size is None or int(r["size"]) <= max_size)]
    rows.sort(key=lambda r: int(r["size"]))
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
            lean, lwall = run([lean_exe, r["path"]])
            rust, rwall = run([rust_exe, r["path"]])
            heads = None
            if lean["status"] == "ok":
                h, _ = run(["python3", "-I", os.path.join(HERE, "heads.py"), r["path"]])
                heads = None if h.get("status") == "crash" else h
            rec = {"path": r["path"], "size": int(r["size"]),
                   "lean": {"status": lean["status"], "reason": lean.get("reason"), "wall": round(lwall, 3)},
                   "rust": {"status": rust["status"], "reason": rust.get("reason"), "wall": round(rwall, 3)},
                   "axiomCounts": lean.get("axiomCounts")}
            if lean["status"] == "ok" and rust["status"] == "ok":
                rec["diffs"] = compare(lean, rust, heads)
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
