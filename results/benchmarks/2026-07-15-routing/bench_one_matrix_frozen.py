#!/usr/bin/env python3
"""Measure one KM or external-baseline classification on an IBEX compute node.

The peak is the sum of RSS over the complete process group, sampled every
40 ms, maxed with GNU time's direct-child peak for sub-sample runs.  The
watchdog applies the same 240 s / 20 GB limits to every procedure. Every
parseable answer is canonicalized and hashed before large outputs are deleted.
Where a retained Konclude signature exists, the answer is also compared to it.
"""

import argparse
import functools
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
    import tree_watchdog as _watchdog
except ModuleNotFoundError:
    # In the repository the canonicalizer and watchdog live under oracle/ore;
    # the frozen IBEX deployment places the same hash-pinned files beside this
    # runner.
    sys.path.insert(
        0,
        os.path.abspath(
            os.path.join(os.path.dirname(__file__), "../../../oracle/ore")
        ),
    )
    import ore_canon as _ore_canon
    import tree_watchdog as _watchdog

ORE_CANON_PATH = os.path.abspath(_ore_canon.__file__)
WATCHDOG_PATH = os.path.abspath(_watchdog.__file__)

UNSUPPORTED_PATTERNS = (
    "unsupported",
    "not supported",
    "not in the profile",
    "outside the profile",
    "owlprofileviolation",
    "cannot handle",
)


def local_name(value):
    return _ore_canon.localname(value)


def load_output(path, output_format):
    try:
        with open(path, encoding="utf-8") as handle:
            text = handle.read()
        consistent, pairs, unsat, capped = _ore_canon.canonicalize(
            text, output_format
        )
        # Keep only the summary consumed by the benchmark row. Parsing the JSON
        # a second time retained a complete duplicate of multi-GB taxonomies
        # beside the canonical pair set (ore_ont_10689), even though no caller
        # uses the full object after canonicalisation.
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
            line = line.rstrip("\n")
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
            # Signature rows are tab-delimited `left\tright` (ore_runone.py's
            # `"\t".join(...)` writer; the same split `ore_aggregate.load_sig`
            # uses). Split on the tab ONLY and keep the leading field: a class
            # whose IRI ends in `#`/`/` has an empty local name, so its row is
            # `\tRIGHT`. The old `line.strip()` + whitespace `line.split()`
            # dropped that field, silently removing the pair from gold and
            # scoring a phantom `extra=1` for EVERY reasoner (ore_ont_11745's
            # `<http://purl.org/obo/owl/UniProtKB#> ⊑ PRO_000003147`, which
            # Konclude, ELK, HermiT, and KM all derive and gold contains).
            if "\t" not in line:
                continue
            left, right = line.split("\t", 1)
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
    if not gold_path or not os.path.exists(gold_path):
        return "nogold", 0, 0, 0, 0, False, data, output_sha
    out_consistent, out_pairs, out_unsat = signature
    missing = 0
    missing_unsat = 0
    matched_pairs = 0
    matched_unsat = 0
    # Gold signatures are sorted and de-duplicated by the ORE harness. Stream
    # them through the output sets instead of materialising a second pair/UNSAT
    # set. Count each match; output_count - matched_count is exactly the
    # output-only (extra) count. This bounds comparison memory to one signature
    # and works with the canonicalizer's immutable frozensets.
    previous_pair = None
    previous_unsat = None
    with gzip.open(gold_path, "rt", encoding="utf-8", errors="replace") as handle:
        first = handle.readline().strip()
        gold_consistent = first == "1"
        in_unsat = False
        for line in handle:
            line = line.rstrip("\n")
            if line == "#UNSAT":
                in_unsat = True
                continue
            if not line:
                continue
            if in_unsat:
                if line == previous_unsat:
                    continue
                previous_unsat = line
                if line in out_unsat:
                    matched_unsat += 1
                else:
                    missing_unsat += 1
                continue
            if "\t" not in line:
                continue
            left, right = line.split("\t", 1)
            if left == right or right in ("Thing", "owlThing", "owlNothing"):
                continue
            pair = (left, right)
            if pair == previous_pair:
                continue
            previous_pair = pair
            if pair in out_pairs:
                matched_pairs += 1
            else:
                missing += 1
    extra = len(out_pairs) - matched_pairs
    extra_unsat = len(out_unsat) - matched_unsat
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

    # The invariant provenance fields are computed up front so a checkpoint row
    # written the instant a limit is crossed already carries everything the
    # sweep's JSON sanity check requires (ont / arm / status / binary_sha256).
    record = {
        "ont": os.path.basename(args.ontology),
        "arm": args.arm,
        "order_index": args.order_index,
        "kind": args.kind,
        "status": "ok",
        "rc": None,
        "wall_s": 0.0,
        "peak_mb": 0.0,
        "host": os.uname().nodename,
        "cpu_model": first_cpu_model(),
        "cpus": int(os.environ.get("SLURM_CPUS_PER_TASK", os.cpu_count() or 1)),
        "slurm_job_id": os.environ.get("SLURM_JOB_ID"),
        "slurm_array_task_id": os.environ.get("SLURM_ARRAY_TASK_ID"),
        "binary_sha256": args.binary_sha or sha256_file(args.binary),
        "runtime_sha256": args.runtime_sha or None,
        "runner_sha256": sha256_file(os.path.abspath(__file__)),
        "canonicalizer_sha256": sha256_file(ORE_CANON_PATH),
        "watchdog_sha256": sha256_file(WATCHDOG_PATH),
        "gold_kind": args.gold_kind,
        "gold_basename": os.path.basename(args.gold) if args.gold else None,
        "gold_sha256": (
            sha256_file(args.gold) if args.gold and os.path.exists(args.gold) else None
        ),
        "signature_sha256": None,
        "requested_route": env.get("KM_ROUTE"),
        "verdict": "ok",
        "extra": 0,
        "missing": 0,
        "extra_unsat": 0,
        "missing_unsat": 0,
        "consistency_mismatch": False,
        "solved": False,
        "checkpointed": False,
    }

    def checkpoint(row):
        """Atomically publish ``row`` to the checkpoint path (if configured).

        Written before the kill on a limit trip so a subsequent whole-cgroup
        OOM kill of this supervisor cannot lose the terminal row; the sbatch
        salvages this file when the runner's stdout is empty.
        """
        if not args.checkpoint:
            return
        tmp = f"{args.checkpoint}.partial.{os.getpid()}"
        try:
            with open(tmp, "w", encoding="utf-8") as handle:
                handle.write(json.dumps(row, sort_keys=True) + "\n")
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(tmp, args.checkpoint)
        except OSError:
            try:
                os.remove(tmp)
            except OSError:
                pass

    def on_trip(trip_status, peak_bytes):
        row = dict(record)
        row.update(
            status=trip_status,
            verdict=trip_status,
            wall_s=round(time.monotonic() - start, 4),
            peak_mb=round(peak_bytes / 1024 / 1024, 2),
            checkpointed=True,
        )
        checkpoint(row)

    def on_hard_alarm(_signum, _frame):
        # Independent of the /proc tree walk: even if a fork storm makes one
        # sampling pass stall, publish a durable timeout before leaving. The
        # batch script then exits and Slurm tears down every remaining child.
        row = dict(record)
        row.update(
            status="timeout",
            verdict="timeout",
            rc=124,
            wall_s=round(time.monotonic() - start, 4),
            checkpointed=True,
        )
        checkpoint(row)
        os._exit(124)

    _watchdog.protect_supervisor()
    stdout_handle = open(stdout_path, "wb")
    stderr_handle = open(stderr_path, "wb")
    start = time.monotonic()
    signal.signal(signal.SIGALRM, on_hard_alarm)
    signal.setitimer(signal.ITIMER_REAL, args.timeout + 5.0)
    proc = subprocess.Popen(
        wrapped,
        env=env,
        stdin=subprocess.DEVNULL,
        stdout=stdout_handle,
        stderr=stderr_handle,
        # Keep the measured RSS cap authoritative. An optional address-space
        # limit is available for diagnostics but stays disabled in production
        # because VMS is not comparable to measured resident memory.
        preexec_fn=(
            functools.partial(
                _watchdog.child_preexec,
                args.hard_as_mb * 1024 * 1024,
            )
            if args.hard_as_mb
            else _watchdog.child_preexec
        ),
    )
    result = _watchdog.monitor(
        proc,
        timeout=args.timeout,
        memcap_bytes=args.memcap_mb * 1024 * 1024,
        sample_interval=0.02,
        on_trip=on_trip,
    )
    signal.setitimer(signal.ITIMER_REAL, 0.0)
    status = result.status
    peak = result.peak_bytes
    wall = result.wall_s
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

    record.update(
        status=status,
        rc=proc.returncode,
        wall_s=round(wall, 4),
        peak_mb=round(peak / 1024 / 1024, 2),
        verdict=status,
    )

    keep_failure = status != "ok" or proc.returncode != 0
    stderr_text = read_text(stderr_path)
    allocation_failed = (
        "memory allocation of " in stderr_text
        or "cannot allocate memory" in stderr_text.lower()
        or "std::bad_alloc" in stderr_text
        or "MemoryError" in stderr_text
        or "oom_kill" in stderr_text.lower()
        or "out of memory" in stderr_text.lower()
    )
    if status == "ok" and proc.returncode != 0 and allocation_failed:
        status = "memout"
        record.update(status=status, verdict=status)
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
    # Overwrite any provisional checkpoint with the fully adjudicated row. The
    # sbatch prefers the runner's stdout row but salvages this file verbatim
    # when the runner was killed after emitting a provisional checkpoint.
    record["checkpointed"] = bool(args.checkpoint)
    checkpoint(record)
    return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--hard-as-mb",
        type=int,
        default=0,
        help="optional per-process RLIMIT_AS spike backstop (disabled by default)",
    )
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
    parser.add_argument(
        "--checkpoint",
        help="path to atomically publish the terminal row to before the kill, "
        "so a whole-cgroup OOM kill of this supervisor cannot lose it",
    )
    parser.add_argument("--env", action="append", default=[])
    args = parser.parse_args()
    if args.gold_kind == "konclude" and not args.gold:
        parser.error("--gold-kind konclude requires --gold")
    if args.gold_kind == "none" and args.gold:
        parser.error("--gold is incompatible with --gold-kind none")
    try:
        record = run(args)
    except Exception as exc:  # noqa: BLE001 - a terminal row must always print
        # run() building its own record makes this path unlikely, but the sweep
        # contract is one publishable row per invocation no matter what. Emit a
        # sanity-check-passing harness_error row (and checkpoint it) rather than
        # exit silently and strand the ontology as permanently unfinished.
        record = {
            "ont": os.path.basename(args.ontology),
            "arm": args.arm,
            "kind": args.kind,
            "status": "harness_error",
            "verdict": "harness_error",
            "rc": None,
            "binary_sha256": args.binary_sha or None,
            "err_tail": repr(exc)[:500],
        }
        if args.checkpoint:
            try:
                with open(args.checkpoint, "w", encoding="utf-8") as handle:
                    handle.write(json.dumps(record, sort_keys=True) + "\n")
            except OSError:
                pass
    print(json.dumps(record, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
