#!/usr/bin/env python3
"""Render ORE tables only after checking their release-bound evidence."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
import statistics
import subprocess


TAG = "v1.3.0"
RELEASE_PATH = "results/benchmarks/2026-08-30-v1.3.0-release/release-gate-summary.json"
PANEL_PATH = "results/benchmarks/2026-07-22-reproduced-route-performance/full-panel-results.scoring-v2.tsv.gz"
CONTRACT_PATH = "results/benchmarks/2026-07-22-reproduced-route-performance/full-panel-contract.tsv"
PANEL_SHA256 = "e2bba1ee660f714b85da1e8db16da4251a59729af2c2de01b3008738c77ebf56"
KM_BINARY_SHA256 = "cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d"
ORDER = ("km", "elk", "konclude", "sequoia_strict", "hermit")
PAIR_ORDER = ("elk", "hermit", "konclude", "sequoia_strict")


def git_bytes(spec: str) -> bytes:
    return subprocess.run(
        ["git", "show", spec], check=True, stdout=subprocess.PIPE
    ).stdout


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def escape(value: str) -> str:
    return value.replace("_", r"\_")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baselines", type=Path, required=True)
    parser.add_argument("--shared", type=Path, required=True)
    parser.add_argument("--shared-detail", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    release_raw = git_bytes(f"{TAG}:{RELEASE_PATH}")
    release = json.loads(release_raw)
    panel_raw = git_bytes(f"{TAG}:{PANEL_PATH}")
    contract_raw = git_bytes(f"{TAG}:{CONTRACT_PATH}")
    shared_raw = args.shared.read_bytes()
    shared = json.loads(shared_raw)

    if release["release"] != TAG:
        raise ValueError("wrong release summary")
    if release["records"] != {"checkpoints": 592, "profiles": 592, "results": 592}:
        raise ValueError("v1.3.0 release records are incomplete")
    if release["status"] != {"error": 1, "ok": 591}:
        raise ValueError("unexpected release status distribution")
    if release["verdict"] != {"consistency_mismatch": 2, "error": 1,
                              "match": 588, "nogold": 1}:
        raise ValueError("unexpected adjudicated release verdict")
    if release["semantic_differences_from_baseline"]:
        raise ValueError("release differs semantically from certified baseline")
    if release["binary_sha256"] != KM_BINARY_SHA256:
        raise ValueError("unexpected release binary")
    if release["metrics"]["correct_completions"] != 591:
        raise ValueError("unexpected KM completion count")
    if digest(panel_raw) != PANEL_SHA256:
        raise ValueError("external panel digest mismatch")
    if shared["km_binary_sha256"] != KM_BINARY_SHA256:
        raise ValueError("shared-correct summary uses another KM binary")
    if set(shared["comparisons"]) != set(PAIR_ORDER):
        raise ValueError("shared-correct comparison set mismatch")

    with args.baselines.open(encoding="utf-8", newline="") as stream:
        rows = {row["id"]: row for row in csv.DictReader(stream, delimiter="\t")}
    if tuple(row for row in ORDER if row not in rows):
        raise ValueError("ORE baseline manifest incomplete")
    if rows["km"]["source_revision"] != subprocess.run(
        ["git", "rev-parse", f"{TAG}^{{}}"], check=True, text=True, stdout=subprocess.PIPE
    ).stdout.strip():
        raise ValueError("KM manifest is not bound to the release tag")
    contract = {
        row["arm"]: row
        for row in csv.DictReader(contract_raw.decode().splitlines(), delimiter="\t")
    }
    for arm in PAIR_ORDER:
        if contract[arm]["source_revision"] != rows[arm]["source_revision"]:
            raise ValueError(f"{arm} revision differs from tagged benchmark contract")

    detail_raw = args.shared_detail.read_bytes()
    detail: dict[str, list[dict[str, str]]] = {arm: [] for arm in PAIR_ORDER}
    with args.shared_detail.open(encoding="utf-8", newline="") as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            if row["arm"] not in detail:
                raise ValueError("unexpected shared-correct detail arm")
            detail[row["arm"]].append(row)
    for arm in PAIR_ORDER:
        rows_for_arm = detail[arm]
        c = shared["comparisons"][arm]
        if len(rows_for_arm) != c["shared_correct_ontologies"]:
            raise ValueError(f"{arm} detail population mismatch")
        for side, prefix in (("km", "km_"), ("external", "external_")):
            expected = c[side]
            walls = [float(row[prefix + "wall_s"]) for row in rows_for_arm]
            peaks = [float(row[prefix + "peak_mib"]) for row in rows_for_arm]
            observed = {
                "n": len(rows_for_arm),
                "mean_wall_s": statistics.fmean(walls),
                "median_wall_s": statistics.median(walls),
                "mean_peak_mib": statistics.fmean(peaks),
                "median_peak_mib": statistics.median(peaks),
            }
            if observed != expected:
                raise ValueError(f"{arm} {side} summary does not reproduce from detail")

    own = {"km": {
        "mean_wall_s": release["metrics"]["mean_wall_s"],
        "median_wall_s": release["metrics"]["median_wall_s"],
        "mean_peak_mib": release["metrics"]["mean_peak_mb"],
        "median_peak_mib": release["metrics"]["median_peak_mb"],
    }}
    for arm in PAIR_ORDER:
        comparison = shared["comparisons"][arm]
        if comparison["shared_correct_ontologies"] != int(rows[arm]["correct_completions"]):
            raise ValueError(f"{arm} correct count differs from shared population")
        own[arm] = comparison["external"]

    release_sha = digest(release_raw)
    shared_sha = digest(shared_raw)
    detail_sha = digest(detail_raw)
    lines = [
        f"% Generated from {TAG}:{RELEASE_PATH} SHA-256 {release_sha}",
        f"% External panel {TAG}:{PANEL_PATH} SHA-256 {PANEL_SHA256}",
        f"% Shared-correct summary SHA-256 {shared_sha}",
        f"% Shared-correct detail SHA-256 {detail_sha}",
        r"\begin{table*}[t]",
        r"\centering",
        r"\small",
        r"\caption{ORE~2015 classification results. Time and memory are over each reasoner's correct completions, not a shared easy subset.}",
        r"\label{tab:benchmark}",
        r"\begin{tabular}{llrrrrr}",
        r"\toprule",
        "Reasoner & Tested version or commit & Correct & Mean s & Median s & Mean MiB & Median MiB \\\\",
        r"\midrule",
    ]
    for arm in ORDER:
        row, metric = rows[arm], own[arm]
        lines.append(
            f'{row["label"]} & {escape(row["version_or_commit"])} & '
            f'{row["correct_completions"]}/592 & {metric["mean_wall_s"]:.4f} & '
            f'{metric["median_wall_s"]:.4f} & {metric["mean_peak_mib"]:.2f} & '
            f'{metric["median_peak_mib"]:.2f} \\\\'
        )
    lines += [
        r"\bottomrule", r"\end{tabular}", r"\end{table*}", "",
        r"\begin{table*}[t]", r"\centering", r"\scriptsize",
        r"\caption{Pairwise shared-correct comparison. Each KM/external pair uses the same $n$ ontologies.}",
        r"\label{tab:shared}", r"\resizebox{\textwidth}{!}{%",
        r"\begin{tabular}{lrrrrrrrrr}", r"\toprule",
        "External reasoner & $n$ & Mean s KM & Mean s ext. & Median s KM & Median s ext. & Mean MiB KM & Mean MiB ext. & Median MiB KM & Median MiB ext. \\\\",
        r"\midrule",
    ]
    for arm in PAIR_ORDER:
        c = shared["comparisons"][arm]
        k, e = c["km"], c["external"]
        lines.append(
            f'{rows[arm]["label"]} & {c["shared_correct_ontologies"]} & '
            f'{k["mean_wall_s"]:.4f} & {e["mean_wall_s"]:.4f} & '
            f'{k["median_wall_s"]:.4f} & {e["median_wall_s"]:.4f} & '
            f'{k["mean_peak_mib"]:.2f} & {e["mean_peak_mib"]:.2f} & '
            f'{k["median_peak_mib"]:.2f} & {e["median_peak_mib"]:.2f} \\\\'
        )
    lines += [r"\bottomrule", r"\end{tabular}}", r"\end{table*}", ""]
    args.output.write_text("\n".join(lines), encoding="utf-8")
    print(f"ORE_TABLES_OK\t{release_sha}\t{PANEL_SHA256}\t{shared_sha}\t{detail_sha}")


if __name__ == "__main__":
    main()
