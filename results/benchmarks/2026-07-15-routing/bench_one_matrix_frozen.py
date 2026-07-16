#!/usr/bin/env python3
"""Measure one KM or external-baseline classification on an IBEX compute node.

The peak is the sum of RSS over the complete process group, sampled every
40 ms, maxed with GNU time's direct-child peak for sub-sample runs.  The
watchdog applies the same 240 s / 20 GB limits to every procedure. Every
parseable answer is canonicalized and hashed before large outputs are deleted.
Where a retained Konclude signature exists, the answer is also compared to it.
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

UNSUPPORTED_PATTERNS = (
    "unsupported",
    "not supported",
    "not in the profile",
    "outside the profile",
    "owlprofileviolation",
    "cannot handle",
)


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


def load_output(path, output_format):
    try:
        with open(path, encoding="utf-8") as handle:
            text = handle.read()
        consistent, pairs, unsat, capped = _ore_canon.canonicalize(
            text, output_format
        )
        if output_format == "json":
            data = json.loads(text)
        else:
            data = {
                "consistent": consistent,
                "subsumption_count": len(pairs),
                "unsatisfiable_count": len(unsat),
            }
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
            line = line.strip()
            if line == "#UNSAT":
                in_unsat = True
                continue
            if not line:
                continue
            if in_unsat:
                # A retained `.sig.gz` is already the canonical local-name
                # signature. Applying `localname` a second time corrupts legal
                # local names containing `/` or `#` (ore_ont_12831).
                unsat.add(line)
                continue
            fields = line.split()
            if len(fields) != 2:
                continue
            left, right = fields
            if left != right and right not in ("Thing", "owlThing", "owlNothing"):
                pairs.add((left, right))
    return consistent, pairs, unsat


def signature_sha256(signature):
    consistent, pairs, unsat = signature
    lines = ["1" if consistent else "0"]
    lines.extend(f"{left}\t{right}" for left, right in sorted(pairs))
    lines.append("#UNSAT")
    lines.extend(sorted(unsat))
    return hashlib.sha256(("\n".join(lines) + "\n").encode("utf-8")).hexdigest()


def compare_output(output, output_format, gold_path):
    signature, data = load_output(output, output_format)
    if signature is None:
        return "noparse", 0, 0, 0, 0, False, None, None
    output_sha = signature_sha256(signature)
    gold = load_gold(gold_path)
    if gold is None:
        return "nogold", 0, 0, 0, 0, False, data, output_sha
    out_consistent, out_pairs, out_unsat = signature
    gold_consistent, gold_pairs, gold_unsat = gold
    extra = len(out_pairs - gold_pairs)
    missing = len(gold_pairs - out_pairs)
    extra_unsat = len(out_unsat - gold_unsat)
    missing_unsat = len(gold_unsat - out_unsat)
    consistency_mismatch = out_consistent != gold_consistent
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
        output_sha,
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


def read_text(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as handle:
            return handle.read()
    except OSError:
        return ""


def run(args):
    os.makedirs(args.workdir, exist_ok=True)
    tag = f"{args.arm}__{os.path.basename(args.ontology)}"
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

    output_format = {
        "km": "json",
        "hermit": "json",
        "elk": "functional",
        "konclude": "owlxml",
    }[args.kind]
    output_path = stdout_path if args.kind in ("km", "hermit") else taxonomy_path

    if args.kind == "km":
        argv = [args.binary, "classify", args.ontology]
    elif args.kind == "konclude":
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
    elif args.kind == "elk":
        argv = [
            args.java,
            args.java_heap,
            "-jar",
            args.binary,
            "-c",
            "-q",
            "-i",
            args.ontology,
            "-o",
            taxonomy_path,
        ]
    else:
        argv = [
            args.java,
            args.java_heap,
            "-cp",
            args.classpath,
            "Oracle",
            args.ontology,
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
        time.sleep(0.04)
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
        "order_index": args.order_index,
        "kind": args.kind,
        "status": status,
        "rc": proc.returncode,
        "wall_s": round(wall, 4),
        "peak_mb": round(peak / 1024 / 1024, 2),
        "host": os.uname().nodename,
        "cpu_model": first_cpu_model(),
        "cpus": int(os.environ.get("SLURM_CPUS_PER_TASK", os.cpu_count() or 1)),
        "slurm_job_id": os.environ.get("SLURM_JOB_ID"),
        "slurm_array_task_id": os.environ.get("SLURM_ARRAY_TASK_ID"),
        "binary_sha256": args.binary_sha or sha256_file(args.binary),
        "runtime_sha256": args.runtime_sha or None,
        "runner_sha256": sha256_file(os.path.abspath(__file__)),
        "canonicalizer_sha256": sha256_file(ORE_CANON_PATH),
        "gold_kind": args.gold_kind,
        "gold_basename": os.path.basename(args.gold) if args.gold else None,
        "gold_sha256": (
            sha256_file(args.gold) if args.gold and os.path.exists(args.gold) else None
        ),
        "signature_sha256": None,
        "requested_route": env.get("KM_ROUTE"),
        "verdict": status,
        "extra": 0,
        "missing": 0,
        "extra_unsat": 0,
        "missing_unsat": 0,
        "consistency_mismatch": False,
        "solved": False,
    }

    keep_failure = status != "ok" or proc.returncode != 0
    stderr_text = read_text(stderr_path)
    unsupported_baseline = args.kind != "km" and any(
        marker in stderr_text.lower() for marker in UNSUPPORTED_PATTERNS
    )
    if status == "ok" and args.kind == "km" and proc.returncode == 3:
        # An atomic mechanism's structural/certificate gate declined. This is a
        # normal fragment result, distinct from a crash and from a timeout; it
        # is ineligible for this ontology but does not need a failure artifact.
        record["status"] = "unsupported"
        record["verdict"] = "unsupported"
        keep_failure = False
    elif status == "ok" and proc.returncode != 0 and unsupported_baseline:
        record["status"] = "unsupported"
        record["verdict"] = "unsupported"
        keep_failure = False
    elif status == "ok" and proc.returncode != 0:
        record["status"] = "error"
        record["verdict"] = "error"
    elif status == "ok":
        (
            verdict,
            extra,
            missing,
            extra_unsat,
            missing_unsat,
            consistency_mismatch,
            data,
            output_sha,
        ) = compare_output(output_path, output_format, args.gold)
        record.update(
            verdict=verdict,
            extra=extra,
            missing=missing,
            extra_unsat=extra_unsat,
            missing_unsat=missing_unsat,
            consistency_mismatch=consistency_mismatch,
            signature_sha256=output_sha,
        )
        if data is not None and "subsumption_count" in data:
            record["consistent"] = bool(data["consistent"])
            record["subsumptions"] = int(data["subsumption_count"])
            record["unsatisfiable"] = int(data["unsatisfiable_count"])
        elif data is not None:
            record["consistent"] = bool(data.get("consistent", True))
            record["subsumptions"] = len(data.get("subsumptions", []))
            record["unsatisfiable"] = len(data.get("unsatisfiable", []))
        if verdict == "noparse" and unsupported_baseline:
            record["status"] = "unsupported"
            record["verdict"] = "unsupported"
            keep_failure = False
            record["solved"] = False
        else:
            # `nogold` only means that canonicalization succeeded. It is not a
            # correctness result; the matrix analyzer may later adjudicate the
            # signature against the independent HermiT row.
            record["solved"] = verdict == "match"
            keep_failure = verdict not in ("match", "nogold")
        if args.kind == "konclude" and record["verdict"] != "unsupported":
            try:
                with open(stdout_path, encoding="utf-8", errors="replace") as handle:
                    log = handle.read()
            except OSError:
                log = ""
            match = re.search(r"expressiveness '([^']+)'", log)
            record["expressivity"] = match.group(1) if match else None
    if keep_failure and args.failures_dir:
        os.makedirs(args.failures_dir, exist_ok=True)
        failure_paths = [stdout_path, stderr_path, time_path]
        if output_path != stdout_path:
            failure_paths.append(output_path)
        for path in failure_paths:
            # A mismatching classifier JSON can be hundreds of megabytes. The
            # row already retains the exact diff cardinalities; preserve stdout
            # only when it is small enough to inspect interactively, while
            # always retaining stderr and GNU-time diagnostics.
            is_primary_output = path == output_path
            if os.path.exists(path) and (
                not is_primary_output or os.path.getsize(path) <= 5 * 1024 * 1024
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
    parser.add_argument(
        "--kind", choices=("km", "konclude", "elk", "hermit"), required=True
    )
    parser.add_argument("--arm", required=True)
    parser.add_argument("--ontology", required=True)
    parser.add_argument("--binary", required=True)
    parser.add_argument("--binary-sha", default="")
    parser.add_argument("--runtime-sha", default="")
    parser.add_argument("--java", default="/usr/bin/java")
    parser.add_argument("--java-heap", default="-Xmx16g")
    parser.add_argument("--classpath", default="")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--order-index", type=int, default=-1)
    parser.add_argument("--timeout", type=float, default=240.0)
    parser.add_argument("--memcap-mb", type=int, default=20480)
    parser.add_argument("--gold")
    parser.add_argument("--gold-kind", choices=("konclude", "none"), default="none")
    parser.add_argument("--workdir", required=True)
    parser.add_argument("--failures-dir")
    parser.add_argument("--env", action="append", default=[])
    args = parser.parse_args()
    if args.gold_kind == "konclude" and not args.gold:
        parser.error("--gold-kind konclude requires --gold")
    if args.gold_kind == "none" and args.gold:
        parser.error("--gold is incompatible with --gold-kind none")
    print(json.dumps(run(args), sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
