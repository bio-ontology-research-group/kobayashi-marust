#!/usr/bin/env python3
"""Compare one retained CB insertion with fresh CB classification of its union."""

import json
import os
import statistics
import subprocess
import sys
import time


def var():
    return {"kind": "var", "name": "x"}


def concept(name):
    return {"kind": "concept", "concept": name, "term": var()}


def subclass(left, right):
    return {"body": [concept(left)], "head": [concept(right)]}


def main():
    if len(sys.argv) != 4:
        raise SystemExit(
            "usage: incremental_cb_microbench.py KM_BINARY CHAINS REPETITIONS"
        )
    binary = sys.argv[1]
    size = int(sys.argv[2])
    repetitions = int(sys.argv[3])

    # The named disjunction selects the CB worker. B_i already occurs in a
    # body, so adding B_0 -> Delta does not change a retained trigger bit and
    # is eligible for exact context-graph replay.
    initial = [
        {
            "body": [concept("Choice")],
            "head": [concept("Left"), concept("Right")],
        }
    ]
    for index in range(size):
        initial.append(subclass(f"A{index}", f"B{index}"))
        initial.append(subclass(f"B{index}", f"C{index}"))
    addition = [subclass("B0", "Delta")]

    environment = os.environ.copy()
    environment["KM_THREADS"] = "1"
    for name in (
        "KM_ELC_CERT",
        "KM_ENGINE_MAX_CONTEXTS",
        "KM_ENGINE_MAX_CLAUSES",
        "KM_MSG_CAP",
        "KM_NOM_BUDGET",
        "KM_NOMINALS",
        "KM_QUERIES",
        "KM_ROOT_ORDERED",
        "KM_SPLIT",
    ):
        environment.pop(name, None)

    init_times = []
    addition_times = []
    fresh_times = []
    last_update = None
    for _ in range(repetitions):
        process = subprocess.Popen(
            [binary, "incremental"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
        )

        def request(value):
            started = time.perf_counter()
            process.stdin.write(
                json.dumps(value, separators=(",", ":")).encode() + b"\n"
            )
            process.stdin.flush()
            response = json.loads(process.stdout.readline())
            assert response["status"] == "ok", response
            return time.perf_counter() - started, response

        elapsed, _ = request({"op": "init", "clauses": initial})
        init_times.append(elapsed)
        elapsed, last_update = request({"op": "add", "clauses": addition})
        addition_times.append(elapsed)
        assert last_update["update"]["strategy"] == "cb_delta", last_update
        assert last_update["update"]["reused_fixpoint"], last_update
        process.stdin.close()
        assert process.wait() == 0, process.stderr.read().decode()

        started = time.perf_counter()
        fresh = subprocess.run(
            [binary, "engine"],
            input=json.dumps(
                {"clauses": initial + addition}, separators=(",", ":")
            ).encode(),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            env=environment,
            check=False,
        )
        fresh_times.append(time.perf_counter() - started)
        assert fresh.returncode == 0, fresh.stderr.decode()

    median_addition = statistics.median(addition_times)
    median_fresh = statistics.median(fresh_times)
    print(
        json.dumps(
            {
                "chains": size,
                "clauses_initial": len(initial),
                "repetitions": repetitions,
                "median_init_seconds": statistics.median(init_times),
                "median_incremental_add_seconds": median_addition,
                "median_fresh_union_seconds": median_fresh,
                "fresh_over_add_ratio": median_fresh / median_addition,
                "update": last_update["update"],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
