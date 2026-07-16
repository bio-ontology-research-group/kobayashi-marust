#!/usr/bin/env python3
"""Audit the final automatic route against paired Konclude references."""

import argparse
import collections
import csv
import glob
import hashlib
import json
import math
import os
import re
import statistics


ADJUDICATED_INCONSISTENT = {
    "ore_ont_2669.owl",
    "ore_ont_10906.owl",
    "ore_ont_15516.owl",
}


def percentile(values, fraction):
    if not values:
        return None
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, math.ceil(fraction * len(ordered)) - 1))
    return ordered[index]


def exact(ont, row):
    if row.get("status") != "ok":
        return False
    if row.get("verdict") in ("match", "nogold"):
        return True
    return ont in ADJUDICATED_INCONSISTENT and row.get("consistent") is False


def reference(row):
    return row.get("status") == "ok" and row.get("verdict") == "reference"


def load_rows(pattern):
    results = {}
    errors = []
    duplicates = []
    paths = sorted(glob.glob(pattern))
    for path in paths:
        for line_number, line in enumerate(open(path, encoding="utf-8"), 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except ValueError as error:
                errors.append({"path": path, "line": line_number, "error": str(error)})
                continue
            ont = row.get("ont")
            arm = row.get("arm")
            if not ont or not arm:
                errors.append({"path": path, "line": line_number, "error": "missing ont/arm"})
                continue
            if arm in results.setdefault(ont, {}):
                duplicates.append({"ont": ont, "arm": arm, "path": path})
            else:
                results[ont][arm] = row
    return results, paths, errors, duplicates


def read_csv_by(path, key):
    if not os.path.exists(path):
        return {}
    return {row[key]: row for row in csv.DictReader(open(path, encoding="utf-8"))}


def sha256_file(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def sha256_profile_directory(path):
    digest = hashlib.sha256()
    paths = sorted(
        glob.glob(os.path.join(path, "*.json")), key=lambda item: os.path.basename(item)
    )
    for profile_path in paths:
        digest.update(os.path.basename(profile_path).encode("utf-8"))
        digest.update(b"\0")
        with open(profile_path, "rb") as handle:
            for block in iter(lambda: handle.read(1 << 20), b""):
                digest.update(block)
        digest.update(b"\0")
    return digest.hexdigest()


def selected_route(trace_dir, ont):
    path = os.path.join(trace_dir, f"auto__{ont}.stderr")
    try:
        text = open(path, encoding="utf-8", errors="replace").read()
    except OSError:
        return None
    match = re.search(r"KM_TIMING frontend done[^\n]* route=([a-z0-9_]+)", text)
    return match.group(1) if match else None


def write_csv(path, rows, fields):
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--expected-km-sha", required=True)
    parser.add_argument("--expected-konclude-sha", required=True)
    parser.add_argument("--expected-canonicalizer-sha", required=True)
    parser.add_argument("--expected-profile-sha", required=True)
    parser.add_argument("--expected-list-sha", required=True)
    parser.add_argument("--expected-runner-sha", required=True)
    args = parser.parse_args()
    root = os.path.abspath(args.root)
    expected = [line.strip() for line in open(os.path.join(root, "onts.txt")) if line.strip()]
    expected_set = set(expected)
    results, paths, parse_errors, duplicates = load_rows(
        os.path.join(root, "auto-paired-results", "*.jsonl")
    )
    predictions = read_csv_by(os.path.join(root, "router-predictions.csv"), "ont")
    profiles = {}
    for path in glob.glob(os.path.join(root, "profiles", "*.json")):
        data = json.load(open(path, encoding="utf-8"))
        profiles[data.get("ont", os.path.basename(path)[:-5])] = data

    missing_files = sorted(expected_set - set(results))
    unexpected = sorted(set(results) - expected_set)
    missing_predictions = sorted(expected_set - set(predictions))
    missing_profiles = sorted(expected_set - set(profiles))
    profile_errors = sorted(
        ont
        for ont in expected_set & set(profiles)
        if profiles[ont].get("status") != "ok"
        or not isinstance(profiles[ont].get("profile"), dict)
    )
    missing_rows = []
    host_mismatches = []
    order_errors = []
    route_missing = []
    route_mismatches = []
    expressivity_mismatches = []
    km_hashes = set()
    konclude_hashes = set()
    canonicalizer_hashes = set()
    cpu_models = set()
    rows_out = []
    trace_dir = os.path.join(root, "auto-failures")

    for ont in expected:
        arms = results.get(ont, {})
        missing = sorted({"auto", "konclude_w1", "konclude_w16"} - set(arms))
        if missing:
            missing_rows.append({"ont": ont, "arms": missing})
            continue
        row_list = list(arms.values())
        hosts = {row.get("host") for row in row_list if row.get("host")}
        if len(hosts) != 1:
            host_mismatches.append({"ont": ont, "hosts": sorted(hosts)})
        order = sorted(row.get("order_index") for row in row_list)
        if order != [0, 1, 2]:
            order_errors.append({"ont": ont, "order": order})
        km_hashes.add(arms["auto"].get("binary_sha256"))
        konclude_hashes.update(
            arms[name].get("binary_sha256") for name in ("konclude_w1", "konclude_w16")
        )
        canonicalizer_hashes.update(
            row.get("canonicalizer_sha256") for row in row_list
        )
        cpu_models.update(row.get("cpu_model") for row in row_list if row.get("cpu_model"))

        route = selected_route(trace_dir, ont)
        if route is None:
            route_missing.append(ont)
        predicted = predictions.get(ont, {}).get("predicted_arm")
        if route is not None and predicted is not None and route != predicted:
            route_mismatches.append({"ont": ont, "rust": route, "analysis": predicted})

        profile = profiles.get(ont, {}).get("profile", {})
        profile_code = profile.get("expressivity", {}).get("code")
        for name in ("konclude_w1", "konclude_w16"):
            official = arms[name].get("expressivity")
            if reference(arms[name]) and official != profile_code:
                expressivity_mismatches.append(
                    {"ont": ont, "arm": name, "km": profile_code, "konclude": official}
                )

        refs = [arms[name] for name in ("konclude_w1", "konclude_w16") if reference(arms[name])]
        best_time = min((row.get("wall_s") for row in refs), default=None)
        best_memory = min((row.get("peak_mb") for row in refs), default=None)
        km = arms["auto"]
        time_ratio = km.get("wall_s") / best_time if exact(ont, km) and best_time else None
        memory_ratio = km.get("peak_mb") / best_memory if exact(ont, km) and best_memory else None
        rows_out.append(
            {
                "ont": ont,
                "route": route,
                "expected_route": predicted,
                "exact": exact(ont, km),
                "status": km.get("status"),
                "verdict": km.get("verdict"),
                "wall_s": km.get("wall_s"),
                "peak_mb": km.get("peak_mb"),
                "konclude_best_wall_s": best_time,
                "konclude_best_peak_mb": best_memory,
                "time_ratio": time_ratio,
                "memory_ratio": memory_ratio,
                "beats_both": bool(
                    time_ratio is not None
                    and memory_ratio is not None
                    and time_ratio < 1.0
                    and memory_ratio < 1.0
                ),
                "over_20_percent": bool(
                    time_ratio is not None
                    and memory_ratio is not None
                    and (time_ratio > 1.2 or memory_ratio > 1.2)
                ),
            }
        )

    reproducibility_errors = []
    observed_profile_sha = sha256_profile_directory(os.path.join(root, "profiles"))
    if observed_profile_sha != args.expected_profile_sha:
        reproducibility_errors.append(
            {
                "profile_corpus_hash_mismatch": {
                    "expected": args.expected_profile_sha,
                    "observed": observed_profile_sha,
                }
            }
        )
    if km_hashes != {args.expected_km_sha}:
        reproducibility_errors.append(
            {
                "km_hash_mismatch": {
                    "expected": args.expected_km_sha,
                    "observed": sorted(str(x) for x in km_hashes),
                }
            }
        )
    if konclude_hashes != {args.expected_konclude_sha}:
        reproducibility_errors.append(
            {
                "konclude_hash_mismatch": {
                    "expected": args.expected_konclude_sha,
                    "observed": sorted(str(x) for x in konclude_hashes),
                }
            }
        )
    if canonicalizer_hashes != {args.expected_canonicalizer_sha}:
        reproducibility_errors.append(
            {
                "canonicalizer_hash_mismatch": {
                    "expected": args.expected_canonicalizer_sha,
                    "observed": sorted(str(x) for x in canonicalizer_hashes),
                }
            }
        )
    observed_list_sha = sha256_file(os.path.join(root, "onts.txt"))
    if observed_list_sha != args.expected_list_sha:
        reproducibility_errors.append(
            {
                "corpus_list_hash_mismatch": {
                    "expected": args.expected_list_sha,
                    "observed": observed_list_sha,
                }
            }
        )
    runner_path = os.path.join(root, "bench_one.py")
    observed_runner_sha = sha256_file(runner_path)
    if observed_runner_sha != args.expected_runner_sha:
        reproducibility_errors.append(
            {
                "runner_hash_mismatch": {
                    "expected": args.expected_runner_sha,
                    "observed": observed_runner_sha,
                }
            }
        )
    if any("Intel(R) Xeon(R) Gold 6248" not in model for model in cpu_models):
        reproducibility_errors.append({"cpu_models": sorted(cpu_models)})
    cpu_allocations = {
        row.get("cpus")
        for arms in results.values()
        for row in arms.values()
        if isinstance(row.get("cpus"), int)
    }
    if cpu_allocations != {16}:
        reproducibility_errors.append(
            {"cpu_allocations": sorted(cpu_allocations)}
        )

    complete = not any(
        (
            parse_errors,
            duplicates,
            missing_files,
            unexpected,
            missing_predictions,
            missing_profiles,
            profile_errors,
            missing_rows,
            host_mismatches,
            order_errors,
            route_missing,
            route_mismatches,
            expressivity_mismatches,
            reproducibility_errors,
        )
    )
    ratios_t = [row["time_ratio"] for row in rows_out if row["time_ratio"] is not None]
    ratios_m = [row["memory_ratio"] for row in rows_out if row["memory_ratio"] is not None]
    summary = {
        "complete": complete,
        "expected_ontologies": len(expected),
        "result_files": len(paths),
        "exact": sum(row["exact"] for row in rows_out),
        "status": dict(collections.Counter(row["status"] for row in rows_out)),
        "verdict": dict(collections.Counter(row["verdict"] for row in rows_out)),
        "routes": dict(collections.Counter(row["route"] for row in rows_out)),
        "beats_konclude_time_and_memory": sum(row["beats_both"] for row in rows_out),
        "over_20_percent": sum(row["over_20_percent"] for row in rows_out),
        "time_ratio": {
            "median": statistics.median(ratios_t) if ratios_t else None,
            "p95": percentile(ratios_t, 0.95),
            "max": max(ratios_t) if ratios_t else None,
        },
        "memory_ratio": {
            "median": statistics.median(ratios_m) if ratios_m else None,
            "p95": percentile(ratios_m, 0.95),
            "max": max(ratios_m) if ratios_m else None,
        },
        "audit": {
            "parse_errors": parse_errors,
            "duplicates": duplicates,
            "missing_files": missing_files,
            "unexpected": unexpected,
            "missing_predictions": missing_predictions,
            "missing_profiles": missing_profiles,
            "profile_errors": profile_errors,
            "missing_rows": missing_rows,
            "host_mismatches": host_mismatches,
            "order_errors": order_errors,
            "route_missing": route_missing,
            "route_mismatches": route_mismatches,
            "expressivity_mismatches": expressivity_mismatches,
            "reproducibility_errors": reproducibility_errors,
            "km_hashes": sorted(str(x) for x in km_hashes),
            "konclude_hashes": sorted(str(x) for x in konclude_hashes),
            "canonicalizer_hashes": sorted(
                str(x) for x in canonicalizer_hashes
            ),
            "cpu_models": sorted(cpu_models),
            "cpu_allocations": sorted(cpu_allocations),
            "corpus_list_sha256": observed_list_sha,
            "runner_sha256": observed_runner_sha,
            "profile_corpus_sha256": observed_profile_sha,
        },
    }
    with open(os.path.join(root, "auto-summary.json"), "w", encoding="utf-8") as handle:
        json.dump(summary, handle, indent=2, sort_keys=True)
        handle.write("\n")
    fields = [
        "ont", "route", "expected_route", "exact", "status", "verdict",
        "wall_s", "peak_mb", "konclude_best_wall_s", "konclude_best_peak_mb",
        "time_ratio", "memory_ratio", "beats_both", "over_20_percent",
    ]
    write_csv(os.path.join(root, "auto-results.csv"), rows_out, fields)
    write_csv(
        os.path.join(root, "auto-over-20-percent.csv"),
        sorted(
            (row for row in rows_out if row["over_20_percent"]),
            key=lambda row: max(row["time_ratio"], row["memory_ratio"]),
            reverse=True,
        ),
        fields,
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    if not complete:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
