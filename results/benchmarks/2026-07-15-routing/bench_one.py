#!/usr/bin/env python3
"""Measure one KM/Konclude classification on an IBEX compute node.

The peak is the sum of RSS over the complete process group, sampled every
40 ms, maxed with GNU time's direct-child peak for sub-sample runs.  The
watchdog applies the same 240 s / 20 GB limits to every procedure.  KM answers
are compared to the retained Konclude signature before large outputs are
deleted.
"""

import argparse
import gzip
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import time

try:
    import ore_canon as _ore_canon
except ModuleNotFoundError:
    # In the repository the canonicalizer lives under oracle/ore; the frozen
    # IBEX deployment places the same hash-pinned file beside this runner.
    sys.path.insert(
        0,
        os.path.abspath(
            os.path.join(os.path.dirname(__file__), "../../../oracle/ore")
        ),
    )
    import ore_canon as _ore_canon

ORE_CANON_PATH = os.path.abspath(_ore_canon.__file__)


def process_group_rss(pgid, page_size):
    total = 0
    try:
        entries = os.listdir("/proc")
    except OSError:
        return 0
    for entry in entries:
        if not entry.isdigit():
            continue
        try:
            with open(f"/proc/{entry}/stat", encoding="ascii") as handle:
                fields = handle.read().split()
            if int(fields[4]) == pgid:
                total += int(fields[23]) * page_size
        except (OSError, IndexError, ValueError):
            pass
    return total


def local_name(value):
    return _ore_canon.localname(value)


def load_km(path):
    try:
        with open(path, encoding="utf-8") as handle:
            text = handle.read()
        consistent, pairs, unsat, capped = _ore_canon.canonicalize(text, "json")
        data = json.loads(text)
    except (OSError, ValueError):
        return None, None
    if capped:
        return None, data
    return (consistent, pairs, unsat), data


def load_gold(path):
    if not path or not os.path.exists(path):
        return None
    pairs = set()
    unsat = set()
    with gzip.open(path, "rt", encoding="utf-8", errors="replace") as handle:
        first = handle.readline().strip()
        consistent = first == "1"
        in_unsat = False
        for line in handle:
            line = line.rstrip("\n")
            if line == "#UNSAT":
                in_unsat = True
                continue
            if not line:
                continue
            if in_unsat:
                unsat.add(local_name(line))
                continue
            # Signature rows are tab-delimited `left\tright` (ore_runone.py's
            # `"\t".join(...)` writer; the same split `ore_aggregate.load_sig`
            # uses). Split on the tab ONLY and keep the leading field: a class
            # whose IRI ends in `#`/`/` has an empty local name, so its row is
            # `\tRIGHT`. The old `line.strip()` + whitespace `line.split()`
            # dropped that field, silently removing the pair from gold and
            # scoring a phantom `extra` for EVERY reasoner (ore_ont_11745's
            # `<http://purl.org/obo/owl/UniProtKB#> ⊑ PRO_000003147`, which
            # Konclude, ELK, HermiT, and KM all derive and gold contains).
            if "\t" not in line:
                continue
            left, right = map(local_name, line.split("\t", 1))
            if left != right and right not in ("Thing", "owlThing", "owlNothing"):
                pairs.add((left, right))
    return consistent, pairs, unsat


def compare_km(output, gold_path):
    km_signature, data = load_km(output)
    if km_signature is None:
        return "nojson", 0, 0, 0, 0, False, None
    gold = load_gold(gold_path)
    if gold is None:
        return "nogold", 0, 0, 0, 0, False, data
    km_consistent, km_pairs, km_unsat = km_signature
    gold_consistent, gold_pairs, gold_unsat = gold
    extra = len(km_pairs - gold_pairs)
    missing = len(gold_pairs - km_pairs)
    extra_unsat = len(km_unsat - gold_unsat)
    missing_unsat = len(gold_unsat - km_unsat)
    consistency_mismatch = km_consistent != gold_consistent
    if not extra and not missing and not extra_unsat and not missing_unsat \
            and not consistency_mismatch:
        verdict = "match"
    elif consistency_mismatch:
        verdict = "consistency_mismatch"
    elif (extra or extra_unsat) and (missing or missing_unsat):
        verdict = "both"
    elif extra or extra_unsat:
        verdict = "unsound"
    else:
        verdict = "incomplete"
    return (
        verdict,
        extra,
        missing,
        extra_unsat,
        missing_unsat,
        consistency_mismatch,
        data,
    )


def first_cpu_model():
    try:
        with open("/proc/cpuinfo", encoding="ascii", errors="replace") as handle:
            for line in handle:
                if line.startswith("model name"):
                    return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return "unknown"


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def run(args):
    os.makedirs(args.workdir, exist_ok=True)
    replicate = f"-r{args.replicate}" if args.replicate else ""
    tag = f"{args.arm}{replicate}__{os.path.basename(args.ontology)}"
    stdout_path = os.path.join(args.workdir, tag + ".stdout")
    stderr_path = os.path.join(args.workdir, tag + ".stderr")
    time_path = os.path.join(args.workdir, tag + ".time")
    taxonomy_path = os.path.join(args.workdir, tag + ".taxonomy.owl")

    env = dict(os.environ)
    for key in list(env):
        if key.startswith("KM_"):
            del env[key]
    for item in args.env:
        if "=" not in item:
            raise ValueError(f"invalid --env {item!r}")
        key, value = item.split("=", 1)
        env[key] = value

    if args.kind == "km":
        argv = [args.binary, "classify", args.ontology]
    else:
        env["LD_LIBRARY_PATH"] = "/ibex/scratch/hohndor/km:" + env.get(
            "LD_LIBRARY_PATH", ""
        )
        argv = [
            args.binary,
            "classification",
            "-w",
            str(args.workers),
            "-v",
            "-i",
            args.ontology,
            "-o",
            taxonomy_path,
        ]
    wrapped = ["/usr/bin/time", "-v", "-o", time_path] + argv

    stdout_handle = open(stdout_path, "wb")
    stderr_handle = open(stderr_path, "wb")
    start = time.monotonic()
    proc = subprocess.Popen(
        wrapped,
        env=env,
        stdin=subprocess.DEVNULL,
        stdout=stdout_handle,
        stderr=stderr_handle,
        start_new_session=True,
    )
    pgid = os.getpgid(proc.pid)
    page_size = os.sysconf("SC_PAGE_SIZE")
    mem_cap = args.memcap_mb * 1024 * 1024
    peak = 0
    status = "ok"
    while proc.poll() is None:
        peak = max(peak, process_group_rss(pgid, page_size))
        elapsed = time.monotonic() - start
        if elapsed > args.timeout:
            status = "timeout"
            break
        if peak > mem_cap:
            status = "memout"
            break
        # `sleep(0.04)` delayed noticing a completed sub-second process until
        # the next RSS tick, quantising wall time in roughly 40 ms steps. Wait
        # on the child for the remainder of the sampling interval instead:
        # completion wakes promptly, while a live child still reaches the same
        # 40 ms process-group RSS and timeout/memcap checks.
        try:
            proc.wait(timeout=0.04)
        except subprocess.TimeoutExpired:
            pass
    if status != "ok":
        try:
            os.killpg(pgid, signal.SIGKILL)
        except OSError:
            pass
    try:
        proc.wait(timeout=15)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(pgid, signal.SIGKILL)
        except OSError:
            pass
        proc.wait()
    peak = max(peak, process_group_rss(pgid, page_size))
    wall = time.monotonic() - start
    stdout_handle.close()
    stderr_handle.close()

    direct_peak = 0
    try:
        with open(time_path, encoding="utf-8", errors="replace") as handle:
            for line in handle:
                if "Maximum resident set size" in line:
                    direct_peak = int(line.rsplit(":", 1)[1].strip()) * 1024
                    break
    except (OSError, ValueError):
        pass
    peak = max(peak, direct_peak)

    record = {
        "ont": os.path.basename(args.ontology),
        "arm": args.arm,
        "replicate": args.replicate,
        "order_index": args.order_index,
        "kind": args.kind,
        "status": status,
        "rc": proc.returncode,
        "wall_s": round(wall, 4),
        "peak_mb": round(peak / 1024 / 1024, 2),
        "host": os.uname().nodename,
        "cpu_model": first_cpu_model(),
        "cpus": int(os.environ.get("SLURM_CPUS_PER_TASK", os.cpu_count() or 1)),
        "binary_sha256": args.binary_sha or sha256_file(args.binary),
        "canonicalizer_sha256": sha256_file(ORE_CANON_PATH),
        "verdict": status,
        "extra": 0,
        "missing": 0,
        "extra_unsat": 0,
        "missing_unsat": 0,
        "consistency_mismatch": False,
        "solved": False,
    }

    keep_failure = args.keep_artifacts or status != "ok" or proc.returncode != 0
    if status == "ok" and proc.returncode != 0:
        record["status"] = "error"
        record["verdict"] = "error"
    elif status == "ok" and args.kind == "km":
        (
            verdict,
            extra,
            missing,
            extra_unsat,
            missing_unsat,
            consistency_mismatch,
            data,
        ) = compare_km(stdout_path, args.gold)
        record.update(
            verdict=verdict,
            extra=extra,
            missing=missing,
            extra_unsat=extra_unsat,
            missing_unsat=missing_unsat,
            consistency_mismatch=consistency_mismatch,
        )
        if data is not None:
            record["consistent"] = bool(data.get("consistent", True))
            record["subsumptions"] = len(data.get("subsumptions", []))
            record["unsatisfiable"] = len(data.get("unsatisfiable", []))
        record["solved"] = verdict in ("match", "nogold")
        keep_failure = args.keep_artifacts or not record["solved"]
    elif status == "ok":
        try:
            with open(stdout_path, encoding="utf-8", errors="replace") as handle:
                log = handle.read()
        except OSError:
            log = ""
        match = re.search(r"expressiveness '([^']+)'", log)
        record["expressivity"] = match.group(1) if match else None
        has_output = os.path.exists(taxonomy_path) and os.path.getsize(taxonomy_path) > 0
        record["verdict"] = "reference" if has_output else "nooutput"
        record["solved"] = record["verdict"] == "reference"
        keep_failure = args.keep_artifacts or not record["solved"]

    if keep_failure and args.failures_dir:
        os.makedirs(args.failures_dir, exist_ok=True)
        for path in (stdout_path, stderr_path, time_path):
            # A mismatching classifier JSON can be hundreds of megabytes. The
            # row already retains the exact diff cardinalities; preserve stdout
            # only when it is small enough to inspect interactively, while
            # always retaining stderr and GNU-time diagnostics.
            is_stdout = path == stdout_path
            if os.path.exists(path) and (
                not is_stdout or os.path.getsize(path) <= 5 * 1024 * 1024
            ):
                shutil.copy2(path, os.path.join(args.failures_dir, os.path.basename(path)))

    for path in (stdout_path, stderr_path, time_path, taxonomy_path):
        try:
            os.remove(path)
        except OSError:
            pass
    return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--kind", choices=("km", "konclude"), required=True)
    parser.add_argument("--arm", required=True)
    parser.add_argument("--ontology", required=True)
    parser.add_argument("--binary", required=True)
    parser.add_argument("--binary-sha", default="")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--order-index", type=int, default=-1)
    parser.add_argument("--replicate", type=int, default=0)
    parser.add_argument("--timeout", type=float, default=240.0)
    parser.add_argument("--memcap-mb", type=int, default=20480)
    parser.add_argument("--gold")
    parser.add_argument("--workdir", required=True)
    parser.add_argument("--failures-dir")
    parser.add_argument("--keep-artifacts", action="store_true")
    parser.add_argument("--env", action="append", default=[])
    args = parser.parse_args()
    print(json.dumps(run(args), sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
