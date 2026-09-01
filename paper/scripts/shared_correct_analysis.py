#!/usr/bin/env python3
"""Compare KM v1.3 with each external reasoner on shared correct ontologies."""

from __future__ import annotations

import argparse
import csv
import gzip
import json
import statistics
from pathlib import Path


ARMS = ("elk", "hermit", "konclude", "sequoia_strict")


def metrics(rows: list[dict[str, object]]) -> dict[str, float | int]:
    walls = [float(row["wall_s"]) for row in rows]
    peaks = [float(row["peak_mib"]) for row in rows]
    return {
        "n": len(rows),
        "mean_wall_s": statistics.fmean(walls),
        "median_wall_s": statistics.median(walls),
        "mean_peak_mib": statistics.fmean(peaks),
        "median_peak_mib": statistics.median(peaks),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--km-results", type=Path, required=True)
    parser.add_argument("--external-panel", type=Path, required=True)
    parser.add_argument("--out-prefix", type=Path, required=True)
    args = parser.parse_args()

    km: dict[str, dict[str, object]] = {}
    for path in args.km_results.glob("ore_ont_*.owl.json"):
        row = json.loads(path.read_text(encoding="utf-8"))
        # The release gate treats the two independently adjudicated consistency
        # mismatches and the retained no-gold completion as correct publications
        # even though the historical ``solved`` field is false for those rows.
        if row.get("status") == "ok":
            km[str(row["ont"])] = {
                "wall_s": float(row["wall_s"]),
                "peak_mib": float(row["peak_mb"]),
            }

    external: dict[str, dict[str, dict[str, object]]] = {arm: {} for arm in ARMS}
    opener = gzip.open if args.external_panel.suffix == ".gz" else open
    with opener(args.external_panel, "rt", encoding="utf-8", newline="") as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            arm = row["arm"]
            if arm not in external:
                continue
            if row["status"] != "ok" or row["sound"] != "yes" or row["complete"] != "yes":
                continue
            external[arm][row["ontology"]] = {
                "wall_s": float(row["wall_s"]),
                "peak_mib": float(row["peak_mb"]),
            }

    summary: dict[str, object] = {
        "km_binary_sha256": "cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d",
        "external_panel": str(args.external_panel),
        "comparisons": {},
    }
    detail_rows: list[dict[str, object]] = []
    for arm in ARMS:
        shared = sorted(set(km) & set(external[arm]))
        km_rows = [km[ontology] for ontology in shared]
        external_rows = [external[arm][ontology] for ontology in shared]
        summary["comparisons"][arm] = {
            "shared_correct_ontologies": len(shared),
            "km": metrics(km_rows),
            "external": metrics(external_rows),
        }
        for ontology in shared:
            detail_rows.append(
                {
                    "arm": arm,
                    "ontology": ontology,
                    "km_wall_s": km[ontology]["wall_s"],
                    "external_wall_s": external[arm][ontology]["wall_s"],
                    "km_peak_mib": km[ontology]["peak_mib"],
                    "external_peak_mib": external[arm][ontology]["peak_mib"],
                }
            )

    args.out_prefix.parent.mkdir(parents=True, exist_ok=True)
    args.out_prefix.with_suffix(".json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    with args.out_prefix.with_suffix(".tsv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=detail_rows[0], delimiter="\t")
        writer.writeheader()
        writer.writerows(detail_rows)

    labels = {"elk": "ELK", "hermit": "HermiT", "konclude": "Konclude", "sequoia_strict": "Sequoia"}
    lines = []
    for arm in ARMS:
        comparison = summary["comparisons"][arm]
        k = comparison["km"]
        e = comparison["external"]
        lines.append(
            f'{labels[arm]} & {comparison["shared_correct_ontologies"]} & '
            f'{k["mean_wall_s"]:.4f} & {e["mean_wall_s"]:.4f} & '
            f'{k["median_wall_s"]:.4f} & {e["median_wall_s"]:.4f} & '
            f'{k["mean_peak_mib"]:.2f} & {e["mean_peak_mib"]:.2f} & '
            f'{k["median_peak_mib"]:.2f} & {e["median_peak_mib"]:.2f} \\\\'
        )
    args.out_prefix.with_suffix(".tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
