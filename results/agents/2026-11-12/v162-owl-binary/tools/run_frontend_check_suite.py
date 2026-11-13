#!/usr/bin/env python3
"""KM_FRONTEND_CHECK suite runner (v1.6.2, plan section 7, phase A).

Runs `km classify --lines` with `KM_FRONTEND_CHECK=1` and
`KM_OWL_REFERENCE_CHECKER=<km-owl-reference>` on a list of inputs and records
per input: km's status and wall time, the check's outcome (agreed, disagreed,
declined, or `-` when km printed no check line), the procedure, the reason or
first differing item, the checker's wall time and its phase timings. Python 3.9
compatible, standard library only.

Usage:

  # pick inputs (F inputs of the v162-parse differential, kind from the survey)
  python3 -I tools/run_frontend_check_suite.py select \
      --parse results/agents/2026-11-12/v162-parse/results.jsonl \
      --survey results/agents/2026-11-12/v162-owl-survey/per_input.tsv \
      --out inputs.tsv [--el-small 8 --el-medium 7 --alc-small 5 --alc-medium 3 \
      --other-f 2 --non-f 5 --max-medium-bytes 20000000]

  # run (resumable: rows already in --out-tsv are skipped)
  python3 -I tools/run_frontend_check_suite.py run \
      --km engine/target/release/km \
      --checker lean/.lake/build/bin/km-owl-reference \
      --inputs inputs.tsv --out-tsv results.tsv --scratch-dir SCRATCH \
      [--jobs 2] [--timeout 300] [--budget 300] [--nice 10]

  python3 -I tools/run_frontend_check_suite.py summarize --tsv results.tsv

`inputs.tsv` has a header and the columns `input` (path) and optionally `kind`
and `size`; any other column is copied through. Each km run gets
`KM_THREADS=1`, `KM_TIMING=1`, a private `TMPDIR` under `--scratch-dir`
(removed afterwards) and no other caller `KM_*` variable.
"""

import argparse
import concurrent.futures as cf
import csv
import json
import os
import random
import re
import signal
import subprocess
import sys
import threading
import time
from collections import Counter

CHECK_RE = re.compile(r"^KM_TIMING KM_FRONTEND_CHECK (agreed|disagreed|declined)(.*)$")
PHASE_RE = re.compile(r"^KM_TIMING KM_FRONTEND_CHECK_PHASE phase=(\S+) ms=(\d+)")
WALL_RE = re.compile(r"^KM_TIMING KM_FRONTEND_CHECK_WALL ms=(\d+)")
ROUTE_RE = re.compile(r"frontend done @ [0-9.]+s route=(\S+)")

FIELDS = [
    "input", "kind", "size", "km_status", "km_wall_s", "route", "check",
    "procedure", "reason", "checker_wall_ms", "checker_phases", "last_err",
]

# Survey heads (v162-owl-survey/per_input.tsv) of the two parts of F.
IGN = {"Prefix", "Ontology", "Declaration", "Class", "ObjectProperty", "DataProperty",
       "NamedIndividual", "AnnotationProperty", "Datatype", "Annotation",
       "AnnotationAssertion", "SubAnnotationPropertyOf", "AnnotationPropertyDomain",
       "AnnotationPropertyRange"}
CLASS_EL = {"SubClassOf", "EquivalentClasses", "ObjectIntersectionOf",
            "ObjectSomeValuesFrom", "ObjectPropertyDomain", "DisjointClasses"}
ROLES_EL = {"SubObjectPropertyOf", "EquivalentObjectProperties",
            "TransitiveObjectProperty", "ObjectPropertyChain"}
CLASS_ALC = CLASS_EL | {"ObjectUnionOf", "ObjectComplementOf", "ObjectAllValuesFrom",
                        "ObjectPropertyRange"}
META = {"input", "size", "p2_status", "route", "prefixes", "full_tokens",
        "pref_tokens", "mixed_entities"}


def survey_kind(row):
    """`el`, `alc` or `other-f` from the survey's construct heads (a
    syntactic guess; the check reports the procedure that answered)."""
    heads = {k for k, v in row.items()
             if k not in META and not k.startswith("kw_") and v and int(v) > 0}
    used = heads - IGN
    if used <= CLASS_EL | ROLES_EL:
        return "el"
    if used <= CLASS_ALC:
        return "alc"
    return "other-f"


def select(args):
    survey = {}
    with open(args.survey, newline="") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            survey[os.path.basename(row["input"])] = row
    f_rows, non_f = [], []
    with open(args.parse) as f:
        for line in f:
            rec = json.loads(line)
            path = rec["path"]
            if not os.path.exists(path):
                continue
            if rec.get("inF") and rec["lean"]["status"] == "ok":
                srow = survey.get(os.path.basename(path))
                kind = survey_kind(srow) if srow else "other-f"
                f_rows.append((path, rec["size"], kind))
            elif not rec.get("inF"):
                non_f.append((path, rec["size"], "non-f"))
    rng = random.Random(args.seed)
    picked = []

    def pick(kind, lo, hi, count):
        pool = sorted((r for r in f_rows if r[2] == kind and lo <= r[1] < hi
                       and r not in picked), key=lambda r: r[1])
        if len(pool) > count:
            # spread over the size range
            step = len(pool) / count
            pool = [pool[int(i * step)] for i in range(count)]
        picked.extend(pool[:count])

    pick("el", 0, args.small_bytes, args.el_small)
    pick("el", args.small_bytes, args.max_medium_bytes, args.el_medium)
    pick("alc", 0, args.small_bytes, args.alc_small)
    pick("alc", args.small_bytes, args.max_medium_bytes, args.alc_medium)
    pick("other-f", 0, args.max_medium_bytes, args.other_f)
    small_non_f = [r for r in non_f if r[1] < args.max_medium_bytes]
    rng.shuffle(small_non_f)
    picked.extend(small_non_f[:args.non_f])
    with open(args.out, "w", newline="") as f:
        w = csv.writer(f, delimiter="\t", lineterminator="\n")
        w.writerow(["input", "kind", "size"])
        for path, size, kind in picked:
            w.writerow([path, kind, size])
    print(f"{len(picked)} inputs: {Counter(r[2] for r in picked)}", file=sys.stderr)


def run_one(km, checker, path, tmp_dir, timeout_s, budget_s, nice):
    os.makedirs(tmp_dir, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}
    env.update({
        "KM_THREADS": "1",
        "KM_TIMING": "1",
        "KM_FRONTEND_CHECK": "1",
        "KM_OWL_REFERENCE_CHECKER": checker,
        "KM_FRONTEND_CHECK_BUDGET_S": str(budget_s),
        "TMPDIR": tmp_dir,
    })
    cmd = [km, "classify", "--lines", path]
    if nice:
        cmd = ["nice", "-n", str(nice)] + cmd
    t0 = time.monotonic()
    proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                            env=env, text=True, errors="replace",
                            start_new_session=True)
    try:
        _, stderr = proc.communicate(timeout=timeout_s)
        status = "ok" if proc.returncode == 0 else "exit%d" % proc.returncode
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        _, stderr = proc.communicate()
        status = "timeout"
    finally:
        subprocess.run(["rm", "-rf", tmp_dir], check=False)
    wall = time.monotonic() - t0
    rec = {"km_status": status, "km_wall_s": "%.3f" % wall, "route": "-",
           "check": "-", "procedure": "-", "reason": "-", "checker_wall_ms": "-",
           "checker_phases": "-", "last_err": "-"}
    phases = []
    for line in stderr.splitlines():
        s = line.strip()
        m = ROUTE_RE.search(s)
        if m:
            rec["route"] = m.group(1)
        m = CHECK_RE.match(s)
        if m:
            rec["check"] = m.group(1)
            rest = m.group(2)
            if m.group(1) == "agreed":
                rec["procedure"] = rest.strip().replace("procedure=", "")
            elif m.group(1) == "disagreed":
                mp = re.search(r"\(procedure=(\S+)\)$", rest)
                if mp:
                    rec["procedure"] = mp.group(1)
                rec["reason"] = re.sub(r"\s*\(procedure=\S+\)$", "", rest.lstrip(": "))[:300]
            else:
                rec["reason"] = rest.lstrip(": ")[:300]
        m = PHASE_RE.match(s)
        if m:
            phases.append("%s:%s" % (m.group(1), m.group(2)))
        m = WALL_RE.match(s)
        if m:
            rec["checker_wall_ms"] = m.group(1)
        if s and not s.startswith("KM_TIMING") and not s.startswith("KM_LEAN_CHECK"):
            rec["last_err"] = s[:300]
    if phases:
        rec["checker_phases"] = ",".join(phases)
    for k in ("reason", "last_err"):
        rec[k] = rec[k].replace("\t", " ")
    return rec


def run_suite(args):
    with open(args.inputs, newline="") as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    os.makedirs(args.scratch_dir, exist_ok=True)
    out_dir = os.path.dirname(os.path.abspath(args.out_tsv))
    os.makedirs(out_dir, exist_ok=True)
    done = set()
    if os.path.exists(args.out_tsv):
        with open(args.out_tsv, newline="") as f:
            done = {r["input"] for r in csv.DictReader(f, delimiter="\t")}
    new_file = not os.path.exists(args.out_tsv)
    out_f = open(args.out_tsv, "a", newline="")
    writer = csv.DictWriter(out_f, fieldnames=FIELDS, delimiter="\t",
                            lineterminator="\n", extrasaction="ignore")
    if new_file:
        writer.writeheader()
        out_f.flush()
    lock = threading.Lock()

    def one(idx_row):
        idx, row = idx_row
        if row["input"] in done:
            return
        tmp = os.path.join(args.scratch_dir, "tmp_%d" % idx)
        while True:
            try:
                rec = run_one(args.km, args.checker, row["input"], tmp,
                              args.timeout, args.budget, args.nice)
                break
            except (MemoryError, OSError) as err:
                print("retry %s: %s" % (row["input"], err), file=sys.stderr)
                time.sleep(60)
        rec.update({"input": row["input"], "kind": row.get("kind", "-"),
                    "size": row.get("size", "-")})
        with lock:
            writer.writerow(rec)
            out_f.flush()
            print("%-60s %-8s %-9s %-5s %s" % (
                os.path.basename(row["input"]), rec["km_status"], rec["check"],
                rec["procedure"], rec["reason"][:80]), file=sys.stderr)

    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        list(ex.map(one, enumerate(rows)))
    out_f.close()


def summarize(args):
    with open(args.tsv, newline="") as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    print("| kind | inputs | km ok | agreed | disagreed | declined | no check line |")
    print("|---|---:|---:|---:|---:|---:|---:|")
    kinds = sorted({r["kind"] for r in rows})
    for kind in kinds + ["all"]:
        rs = [r for r in rows if kind == "all" or r["kind"] == kind]
        c = Counter(r["check"] for r in rs)
        ok = sum(1 for r in rs if r["km_status"] == "ok")
        print("| %s | %d | %d | %d | %d | %d | %d |" % (
            kind, len(rs), ok, c["agreed"], c["disagreed"], c["declined"], c["-"]))
    print()
    print("Procedures of agreements:", dict(Counter(r["procedure"] for r in rows
                                                    if r["check"] == "agreed")))
    reasons = Counter(re.sub(r" \(checker status:.*|\(clause \d+.*", "", r["reason"])[:110]
                      for r in rows if r["check"] == "declined")
    print()
    print("| decline reason | inputs |")
    print("|---|---:|")
    for reason, n in reasons.most_common():
        print("| %s | %d |" % (reason.replace("|", "/"), n))
    dis = [r for r in rows if r["check"] == "disagreed"]
    if dis:
        print()
        print("Disagreements:")
        for r in dis:
            print("- %s: %s" % (os.path.basename(r["input"]), r["reason"]))
    print()
    print("| input | kind | MB | km status | km wall s | check | procedure | checker ms | phases (ms) |")
    print("|---|---|---:|---|---:|---|---|---:|---|")
    for r in sorted(rows, key=lambda r: (r["kind"], int(r["size"]) if r["size"].isdigit() else 0)):
        mb = "%.1f" % (int(r["size"]) / 1e6) if r["size"].isdigit() else "-"
        print("| %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            os.path.basename(r["input"]), r["kind"], mb, r["km_status"], r["km_wall_s"],
            r["check"], r["procedure"], r["checker_wall_ms"], r["checker_phases"]))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd")
    s = sub.add_parser("select")
    s.add_argument("--parse", required=True)
    s.add_argument("--survey", required=True)
    s.add_argument("--out", required=True)
    s.add_argument("--el-small", type=int, default=8)
    s.add_argument("--el-medium", type=int, default=7)
    s.add_argument("--alc-small", type=int, default=5)
    s.add_argument("--alc-medium", type=int, default=3)
    s.add_argument("--other-f", type=int, default=2)
    s.add_argument("--non-f", type=int, default=5)
    s.add_argument("--small-bytes", type=int, default=200000)
    s.add_argument("--max-medium-bytes", type=int, default=20000000)
    s.add_argument("--seed", type=int, default=162)
    r = sub.add_parser("run")
    r.add_argument("--km", required=True)
    r.add_argument("--checker", required=True)
    r.add_argument("--inputs", required=True)
    r.add_argument("--out-tsv", required=True)
    r.add_argument("--scratch-dir", required=True)
    r.add_argument("--jobs", type=int, default=2)
    r.add_argument("--timeout", type=int, default=300)
    r.add_argument("--budget", type=float, default=300)
    r.add_argument("--nice", type=int, default=10)
    m = sub.add_parser("summarize")
    m.add_argument("--tsv", required=True)
    args = ap.parse_args()
    if args.cmd == "select":
        select(args)
    elif args.cmd == "run":
        args.km = os.path.abspath(args.km)
        args.checker = os.path.abspath(args.checker)
        run_suite(args)
    elif args.cmd == "summarize":
        summarize(args)
    else:
        ap.print_help()
        sys.exit(2)


if __name__ == "__main__":
    main()
