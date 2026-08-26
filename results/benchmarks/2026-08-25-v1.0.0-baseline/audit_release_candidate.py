#!/usr/bin/env python3
"""Fail-closed v1.1 aggregate release gate for a complete Gold sweep."""

from __future__ import annotations

import argparse
import csv
import json
import statistics
from pathlib import Path


GOLD_CPU = "Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"
EXPECTED_SPECIAL = {
    "ore_ont_2669.owl": "consistency_mismatch",
    "ore_ont_15516.owl": "consistency_mismatch",
    "ore_ont_10860.owl": "nogold",
}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--binary-sha256", required=True)
    parser.add_argument("--v1-ledger", type=Path, required=True)
    parser.add_argument("--recovery-ledger", type=Path, required=True)
    parser.add_argument("--external-aggregates", type=Path, required=True)
    args = parser.parse_args()

    with args.v1_ledger.open(newline="") as stream:
        baseline = {
            row["ontology"]: row for row in csv.DictReader(stream, delimiter="\t")
        }
    with args.recovery_ledger.open(newline="") as stream:
        recovery = {
            row["ontology"]: row for row in csv.DictReader(stream, delimiter="\t")
        }
    external = json.loads(args.external_aggregates.read_text())["arms"]
    result_dir = args.root / "results"
    errors: list[str] = []
    rows: dict[str, dict] = {}

    temporary = sorted(args.root.rglob("*.tmp"))
    if temporary:
        errors.append(f"temporary outputs remain: {temporary[:5]}")
    for terminal in sorted(result_dir.glob("ore_ont_*.owl.json")):
        if terminal.name.endswith(".checkpoint.json"):
            continue
        name = terminal.name[:-len(".json")]
        checkpoint = terminal.with_name(f"{name}.checkpoint.json")
        if not checkpoint.is_file() or checkpoint.read_bytes() != terminal.read_bytes():
            errors.append(f"checkpoint missing or different: {name}")
            continue
        row = json.loads(terminal.read_text())
        if name in rows:
            errors.append(f"duplicate ontology: {name}")
            continue
        rows[name] = row
        prior = baseline.get(name)
        if prior is None:
            errors.append(f"ontology absent from v1 ledger: {name}")
            continue
        if row.get("ont") != name:
            errors.append(f"ontology/path mismatch: {name}")
        if row.get("binary_sha256") != args.binary_sha256:
            errors.append(f"binary mismatch: {name}")
        if row.get("cpu_model") != GOLD_CPU:
            errors.append(f"non-Gold CPU: {name}: {row.get('cpu_model')}")
        if row.get("checkpointed") is not True:
            errors.append(f"checkpoint flag absent: {name}")
        profile_path = args.root / "profiles" / f"{name}.json"
        if not profile_path.is_file():
            errors.append(f"missing route profile: {name}")
        else:
            profile = json.loads(profile_path.read_text())
            if profile.get("ont") != name or profile.get("status") != "ok":
                errors.append(f"invalid route profile: {name}")
            if prior["status"] == "ok" and not profile.get("selected_route"):
                errors.append(f"profile lacks selected route: {name}")
        if row.get("status") != prior["status"]:
            recovered = recovery.get(name)
            valid_recovery = (
                prior["status"] != "ok"
                and row.get("status") == "ok"
                and recovered is not None
                and recovered.get("status") == "ok"
                and recovered.get("verdict") == "match"
                and row.get("signature_sha256")
                == recovered.get("signature_sha256")
            )
            if not valid_recovery:
                errors.append(
                    f"unproved v1 status change: {name}: "
                    f"{prior['status']} -> {row.get('status')}"
                )
        if prior["status"] == "ok":
            if row.get("signature_sha256") != prior["signature_sha256"]:
                errors.append(f"v1 signature changed: {name}")
            expected_verdict = EXPECTED_SPECIAL.get(name, "match")
            if row.get("verdict") != expected_verdict:
                errors.append(
                    f"wrong adjudicated verdict: {name}: {row.get('verdict')}"
                )
            for key in ("wall_s", "peak_mb", "selected_route_trace"):
                if row.get(key) in (None, ""):
                    errors.append(f"missing {key}: {name}")
        elif row.get("status") == "ok":
            # The status-transition gate above has already bound this answer to
            # the independent recovery signature. Apply the same publication
            # evidence requirements as every baseline success.
            for key in ("wall_s", "peak_mb", "selected_route_trace"):
                if row.get(key) in (None, ""):
                    errors.append(f"missing recovered {key}: {name}")

    missing = sorted(set(baseline) - set(rows))
    extra = sorted(set(rows) - set(baseline))
    if missing:
        errors.append(
            f"missing ontology rows ({len(missing)}): " + ", ".join(missing[:10])
        )
    if extra:
        errors.append(
            f"unexpected ontology rows ({len(extra)}): " + ", ".join(extra[:10])
        )
    successful = [row for row in rows.values() if row.get("status") == "ok"]
    if len(rows) != 592 or len(successful) != 591:
        errors.append(f"wrong coverage: terminal={len(rows)} successful={len(successful)}")

    walls = [float(row["wall_s"]) for row in successful if row.get("wall_s") is not None]
    peaks = [float(row["peak_mb"]) for row in successful if row.get("peak_mb") is not None]
    metrics = {
        "mean_wall_s": sum(walls) / len(walls) if walls else float("inf"),
        "median_wall_s": statistics.median(walls) if walls else float("inf"),
        "mean_peak_mib": sum(peaks) / len(peaks) if peaks else float("inf"),
        "median_peak_mib": statistics.median(peaks) if peaks else float("inf"),
    }
    comparisons: dict[str, dict[str, bool]] = {}
    for arm, target in sorted(external.items()):
        comparisons[arm] = {
            key: metrics[key] < float(target[key]) for key in metrics
        }
        for key, passed in comparisons[arm].items():
            if not passed:
                errors.append(
                    f"aggregate gate failed: {key}={metrics[key]:.6f} "
                    f">= {arm}={float(target[key]):.6f}"
                )

    print(json.dumps({
        "terminal": len(rows),
        "successful": len(successful),
        "metrics": metrics,
        "comparisons": comparisons,
        "errors": len(errors),
    }, indent=2, sort_keys=True))
    for error in errors:
        print(f"ERROR {error}")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
