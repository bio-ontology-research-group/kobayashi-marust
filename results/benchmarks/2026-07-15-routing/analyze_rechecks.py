#!/usr/bin/env python3
"""Aggregate the three paired repeats for matrix gaps above 20 percent."""

import argparse
import collections
import csv
import glob
import hashlib
import json
import os
import statistics


ADJUDICATED_INCONSISTENT = {
    "ore_ont_2669.owl",
    "ore_ont_10906.owl",
    "ore_ont_15516.owl",
}


def exact(ont, row):
    return row.get("status") == "ok" and (
        row.get("verdict") in ("match", "nogold")
        or (ont in ADJUDICATED_INCONSISTENT and row.get("consistent") is False)
    )


def reference(row):
    return row.get("status") == "ok" and row.get("verdict") == "reference"


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--replicates", type=int, default=3)
    parser.add_argument("--mode", choices=("oracle", "auto"), default="oracle")
    parser.add_argument("--expected-km-sha", required=True)
    parser.add_argument("--expected-konclude-sha", required=True)
    parser.add_argument("--expected-runner-sha", required=True)
    args = parser.parse_args()
    root = os.path.abspath(args.root)
    gaps_name = (
        "gaps-over-20-percent.csv"
        if args.mode == "oracle"
        else "auto-over-20-percent.csv"
    )
    gaps = {
        row["ont"]: row
        for row in csv.DictReader(open(os.path.join(root, gaps_name)))
    }
    prefix = "gap" if args.mode == "oracle" else "auto-gap"
    by_ont = collections.defaultdict(list)
    parse_errors = []
    for path in glob.glob(os.path.join(root, f"{prefix}-rechecks", "*.jsonl")):
        for line_number, line in enumerate(open(path, encoding="utf-8"), 1):
            try:
                row = json.loads(line)
                by_ont[row["ont"]].append(row)
            except (ValueError, KeyError) as error:
                parse_errors.append({"path": path, "line": line_number, "error": str(error)})

    audit_errors = []
    output = []
    for ont, gap in gaps.items():
        arm = gap["oracle_arm"] if args.mode == "oracle" else "auto"
        rows = by_ont.get(ont, [])
        ratios_t = []
        ratios_m = []
        km_walls = []
        km_peaks = []
        for replicate in range(1, args.replicates + 1):
            batch = [row for row in rows if row.get("replicate") == replicate]
            grouped = collections.defaultdict(list)
            for row in batch:
                grouped[row.get("arm")].append(row)
            wanted = {arm, "konclude_w1", "konclude_w16"}
            if set(grouped) != wanted or any(len(grouped[name]) != 1 for name in wanted):
                audit_errors.append(
                    {"ont": ont, "replicate": replicate, "arms": {k: len(v) for k, v in grouped.items()}}
                )
                continue
            km = grouped[arm][0]
            refs = [grouped["konclude_w1"][0], grouped["konclude_w16"][0]]
            all_rows = [km] + refs
            hosts = {row.get("host") for row in all_rows}
            order = sorted(row.get("order_index") for row in all_rows)
            km_hash = km.get("binary_sha256")
            konclude_hashes = {row.get("binary_sha256") for row in refs}
            cpu_models = {row.get("cpu_model") for row in all_rows}
            cpu_allocations = {row.get("cpus") for row in all_rows}
            if (
                len(hosts) != 1
                or order != [0, 1, 2]
                or km_hash != args.expected_km_sha
                or konclude_hashes != {args.expected_konclude_sha}
                or any("Intel(R) Xeon(R) Gold 6248" not in str(m) for m in cpu_models)
                or cpu_allocations != {16}
            ):
                audit_errors.append(
                    {
                        "ont": ont,
                        "replicate": replicate,
                        "hosts": sorted(str(value) for value in hosts),
                        "order": order,
                        "km_hash": km_hash,
                        "konclude_hashes": sorted(str(value) for value in konclude_hashes),
                        "cpu_models": sorted(str(value) for value in cpu_models),
                        "cpu_allocations": sorted(str(value) for value in cpu_allocations),
                    }
                )
                continue
            if not exact(ont, km) or not all(reference(row) for row in refs):
                audit_errors.append(
                    {
                        "ont": ont,
                        "replicate": replicate,
                        "km": [km.get("status"), km.get("verdict")],
                        "references": [[row.get("status"), row.get("verdict")] for row in refs],
                    }
                )
                continue
            best_time = min(row["wall_s"] for row in refs)
            best_memory = min(row["peak_mb"] for row in refs)
            ratios_t.append(km["wall_s"] / best_time)
            ratios_m.append(km["peak_mb"] / best_memory)
            km_walls.append(km["wall_s"])
            km_peaks.append(km["peak_mb"])
        median_t = statistics.median(ratios_t) if ratios_t else None
        median_m = statistics.median(ratios_m) if ratios_m else None
        output.append(
            {
                "ont": ont,
                "arm": arm,
                "replicates": len(ratios_t),
                "initial_time_ratio": gap["time_ratio"],
                "initial_memory_ratio": gap["memory_ratio"],
                "median_wall_s": statistics.median(km_walls) if km_walls else None,
                "median_peak_mb": statistics.median(km_peaks) if km_peaks else None,
                "median_time_ratio": median_t,
                "median_memory_ratio": median_m,
                "confirmed_over_20_percent": bool(
                    median_t is not None
                    and median_m is not None
                    and (median_t > 1.2 or median_m > 1.2)
                ),
                "trace_directory": os.path.join(f"{prefix}-artifacts", ont),
            }
        )

    fields = [
        "ont", "arm", "replicates", "initial_time_ratio", "initial_memory_ratio",
        "median_wall_s", "median_peak_mb", "median_time_ratio", "median_memory_ratio",
        "confirmed_over_20_percent", "trace_directory",
    ]
    output.sort(
        key=lambda row: max(row["median_time_ratio"] or 0, row["median_memory_ratio"] or 0),
        reverse=True,
    )
    csv_path = os.path.join(root, f"{prefix}-recheck-summary.csv")
    with open(csv_path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(output)
    runner_sha = sha256_file(os.path.join(root, "bench_one.py"))
    if runner_sha != args.expected_runner_sha:
        audit_errors.append(
            {
                "runner_hash_mismatch": {
                    "expected": args.expected_runner_sha,
                    "observed": runner_sha,
                }
            }
        )
    summary = {
        "complete": not parse_errors and not audit_errors and len(output) == len(gaps),
        "expected": len(gaps),
        "rows": len(output),
        "confirmed_over_20_percent": sum(row["confirmed_over_20_percent"] for row in output),
        "parse_errors": parse_errors,
        "audit_errors": audit_errors,
        "runner_sha256": runner_sha,
    }
    json_path = os.path.join(root, f"{prefix}-recheck-summary.json")
    with open(json_path, "w", encoding="utf-8") as handle:
        json.dump(summary, handle, indent=2, sort_keys=True)
        handle.write("\n")
    print(json.dumps(summary, indent=2, sort_keys=True))
    if not summary["complete"]:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
