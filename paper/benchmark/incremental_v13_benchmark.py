#!/usr/bin/env python3
"""Exact-v1.3 EL/CB retained-update scale check with raw repetitions."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import tempfile
import time


EXPECTED_BINARY = "cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def var() -> dict:
    return {"kind": "var", "name": "x"}


def concept(name: str) -> dict:
    return {"kind": "concept", "concept": name, "term": var()}


def subclass(left: str, right: str) -> dict:
    return {"body": [concept(left)], "head": [concept(right)]}


def inputs(case: str, size: int) -> tuple[list[dict], list[dict], str, str]:
    if case == "el":
        return ([subclass(f"A{i}", f"B{i}") for i in range(size)],
                [subclass("B0", "C")], "el", "el_delta")
    initial = [{"body": [concept("Choice")],
                "head": [concept("Left"), concept("Right")]}]
    for index in range(size):
        initial.extend((subclass(f"A{index}", f"B{index}"),
                        subclass(f"B{index}", f"C{index}")))
    return initial, [subclass("B0", "Delta")], "cb", "cb_delta"


def semantic_projection(value: dict) -> dict:
    return {
        "subsumptions": value["subsumptions"],
        "inconsistent": value["inconsistent"],
        "unresolved": value.get("unresolved", []),
    }


def parse_time(path: Path) -> int:
    fields = dict(line.split("=", 1) for line in path.read_text().splitlines())
    return int(fields["max_rss_kb"])


def measured_run(binary: Path, case: str, size: int, environment: dict[str, str]) -> dict:
    initial, addition, backend, strategy = inputs(case, size)
    union = {"clauses": initial + addition}
    with tempfile.TemporaryDirectory() as temporary:
        temporary_path = Path(temporary)
        incremental_time = temporary_path / "incremental.time"
        process = subprocess.Popen(
            ["/usr/bin/time", "-f", "max_rss_kb=%M", "-o", str(incremental_time),
             str(binary), "incremental"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment,
        )

        def request(payload: dict) -> tuple[float, dict]:
            started = time.perf_counter_ns()
            assert process.stdin is not None and process.stdout is not None
            process.stdin.write(json.dumps(payload, separators=(",", ":")).encode() + b"\n")
            process.stdin.flush()
            response = json.loads(process.stdout.readline())
            elapsed = (time.perf_counter_ns() - started) / 1_000_000_000
            if response.get("status") != "ok":
                raise RuntimeError(f"incremental request failed: {response}")
            return elapsed, response

        init_s, init = request({"op": "init", "clauses": initial})
        add_s, update = request({"op": "add", "clauses": addition})
        classify_s, classified = request({"op": "classify"})
        assert init["backend"] == backend, init
        assert update["update"]["strategy"] == strategy, update
        assert update["update"]["reused_fixpoint"] is True, update
        assert classified["backend"] == backend, classified
        assert process.stdin is not None
        process.stdin.close()
        rc = process.wait()
        stderr = process.stderr.read().decode() if process.stderr is not None else ""
        if rc != 0:
            raise RuntimeError(f"incremental process failed ({rc}): {stderr}")

        fresh_time = temporary_path / "fresh.time"
        started = time.perf_counter_ns()
        fresh = subprocess.run(
            ["/usr/bin/time", "-f", "max_rss_kb=%M", "-o", str(fresh_time),
             str(binary), "elc" if case == "el" else "engine"],
            input=json.dumps(union, separators=(",", ":")).encode(),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=environment,
            check=False,
        )
        fresh_s = (time.perf_counter_ns() - started) / 1_000_000_000
        if fresh.returncode != 0:
            raise RuntimeError(f"fresh process failed ({fresh.returncode}): "
                               + fresh.stderr.decode())
        fresh_result = json.loads(fresh.stdout)
        incremental_result = classified["result"]
        if incremental_result.get("dropped", 0) != 0 or fresh_result.get("dropped", 0) != 0:
            raise RuntimeError("comparison includes a dropped-clause result")
        if semantic_projection(incremental_result) != semantic_projection(fresh_result):
            raise RuntimeError("incremental and fresh classifications differ")
        result_sha256 = hashlib.sha256(json.dumps(
            semantic_projection(fresh_result), sort_keys=True,
            separators=(",", ":")).encode()).hexdigest()
        return {
            "init_s": init_s,
            "incremental_add_s": add_s,
            "incremental_classify_s": classify_s,
            "fresh_union_s": fresh_s,
            "incremental_process_peak_kib": parse_time(incremental_time),
            "fresh_process_peak_kib": parse_time(fresh_time),
            "strategy": strategy,
            "reused_fixpoint": True,
            "reused_subsumptions": update["update"]["reused_subsumptions"],
            "new_subsumptions": update["update"]["new_subsumptions"],
            "semantic_result_sha256": result_sha256,
        }


def median(rows: list[dict], key: str) -> float:
    return statistics.median(row[key] for row in rows)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--repetitions", type=int, default=10)
    parser.add_argument("--el-size", type=int, default=10_000)
    parser.add_argument("--cb-chains", type=int, default=500)
    args = parser.parse_args()
    if digest(args.binary) != EXPECTED_BINARY:
        raise SystemExit("binary digest is not the exact v1.3 benchmark artifact")
    if args.warmups < 0 or args.repetitions < 3:
        raise SystemExit("require nonnegative warmups and at least three repetitions")

    environment = {
        "PATH": "/usr/bin:/bin",
        "LC_ALL": "C",
        "KM_THREADS": "1",
        "RAYON_NUM_THREADS": "1",
    }
    cases = {}
    for case, size in (("el", args.el_size), ("cb", args.cb_chains)):
        all_rows = [measured_run(args.binary, case, size, environment)
                    for _ in range(args.warmups + args.repetitions)]
        rows = all_rows[args.warmups:]
        if len({row["semantic_result_sha256"] for row in rows}) != 1:
            raise RuntimeError(f"nondeterministic semantic result for {case}")
        cases[case] = {
            "size": size,
            "warmup_rows": all_rows[:args.warmups],
            "measured_rows": rows,
            "medians": {
                key: median(rows, key) for key in (
                    "init_s", "incremental_add_s", "incremental_classify_s",
                    "fresh_union_s", "incremental_process_peak_kib",
                    "fresh_process_peak_kib")
            },
            "fresh_over_incremental_add_ratio": (
                median(rows, "fresh_union_s") / median(rows, "incremental_add_s")),
        }
    payload = {
        "schema": 1,
        "binary_sha256": digest(args.binary),
        "runner_sha256": digest(Path(__file__)),
        "warmups": args.warmups,
        "repetitions": args.repetitions,
        "controlled_environment": environment,
        "comparison_scope": (
            "Incremental add measures one request inside an initialized process; "
            "fresh union includes process startup, parsing, classification, and serialization. "
            "Incremental peak covers initialization plus update."),
        "cases": cases,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(args.output) + ".part")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    temporary.replace(args.output)
    print(f"INCREMENTAL_V13_OK\t{args.output}")


if __name__ == "__main__":
    main()
