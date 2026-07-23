#!/usr/bin/env python3
"""Re-score a retained ORE panel without rerunning any reasoner.

The raw status, time, memory, fingerprints, commands, and provenance remain
unchanged.  Only correctness fields are recomputed through the versioned
semantic scorer in ``full_panel_correctness.py``.  New panels should run this
as their mandatory final aggregation step, even if the per-ontology driver
also writes provisional correctness fields.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import gzip
import hashlib
import json
from pathlib import Path
import statistics

from full_panel_correctness import (
    apply_retained_targeted_adjudication,
    classify_correctness,
)


STANDARD_ARMS = {
    "km_auto": "km_route_auto",
    "konclude": "konclude",
    "hermit": "hermit",
    "elk": "elk",
    "rustdl": "rustdl_complete",
    "sequoia": "sequoia_strict",
}
CORRECTNESS_FIELDS = ("sound", "complete", "solved", "correctness_basis")
BOOLEAN_FIELDS = (
    "solved",
    "fulliri_identity_capable",
    "localname_identity_capable",
    "consistent",
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_bool(value: object) -> object:
    if not isinstance(value, str):
        return value
    lowered = value.strip().lower()
    if lowered == "true":
        return True
    if lowered == "false":
        return False
    return value


def bool_text(value: object) -> str:
    if value is True:
        return "True"
    if value is False:
        return "False"
    return "" if value is None else str(value)


def metric(rows: list[dict], field: str, operation) -> float | None:
    values = [
        float(row[field])
        for row in rows
        if row.get("status") == "ok" and row.get(field) not in (None, "")
    ]
    return round(operation(values), 4) if values else None


def summarize(label: str, rows: list[dict]) -> dict:
    status = Counter(row.get("status") for row in rows)
    return {
        "procedure": label,
        "rows": len(rows),
        "sound_yes": sum(row.get("sound") == "yes" for row in rows),
        "complete_yes": sum(row.get("complete") == "yes" for row in rows),
        "sound_and_complete_yes": sum(
            row.get("sound") == row.get("complete") == "yes" for row in rows
        ),
        "status_ok": status["ok"],
        "status_timeout": status["timeout"],
        "status_memout": status["memout"],
        "status_error": sum(
            count
            for key, count in status.items()
            if key not in {"ok", "timeout", "memout", "unsupported", "no_claim"}
        ),
        "status_unsupported": status["unsupported"],
        "wall_mean_s_status_ok": metric(rows, "wall_s", statistics.mean),
        "wall_median_s_status_ok": metric(rows, "wall_s", statistics.median),
        "peak_mean_mib_status_ok": metric(rows, "peak_mb", statistics.mean),
        "peak_median_mib_status_ok": metric(rows, "peak_mb", statistics.median),
    }


def write_tsv(path: Path, rows: list[dict], fields: list[str]) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)
    temporary.replace(path)


def write_gzip_tsv(path: Path, rows: list[dict], fields: list[str]) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("wb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as compressed:
            import io

            with io.TextIOWrapper(compressed, encoding="utf-8", newline="") as text:
                writer = csv.DictWriter(
                    text, fieldnames=fields, delimiter="\t", lineterminator="\n"
                )
                writer.writeheader()
                for row in rows:
                    writer.writerow(
                        {
                            field: bool_text(row.get(field))
                            if field in BOOLEAN_FIELDS
                            else row.get(field, "")
                            for field in fields
                        }
                    )
    temporary.replace(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--wide", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--contract",
        type=Path,
        help="procedure TSV (default: OUTPUT_DIR/full-panel-contract.tsv)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    contract_path = args.contract or args.output_dir / "full-panel-contract.tsv"
    with contract_path.open(newline="", encoding="utf-8") as handle:
        contract_reader = csv.DictReader(handle, delimiter="\t")
        contract_rows = list(contract_reader)
    expected_arms = [row.get("arm", "") for row in contract_rows]
    if not expected_arms or any(not arm for arm in expected_arms):
        raise SystemExit(f"invalid or empty procedure contract: {contract_path}")
    if len(expected_arms) != len(set(expected_arms)):
        raise SystemExit(f"duplicate procedure arm in contract: {contract_path}")
    if "konclude" not in expected_arms:
        raise SystemExit("procedure contract lacks the Konclude reference arm")

    with gzip.open(args.input, "rt", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        fields = list(reader.fieldnames or [])
        rows = list(reader)
    if not fields or "ontology" not in fields or "arm" not in fields:
        raise SystemExit("input is not a full-panel long table")
    expected_row_count = 592 * len(expected_arms)
    if len(rows) != expected_row_count:
        raise SystemExit(
            f"expected {expected_row_count:,} rows from the "
            f"{len(expected_arms)}-procedure contract, found {len(rows):,}"
        )

    by_ontology: dict[str, list[dict]] = defaultdict(list)
    for row in rows:
        row["ont"] = row["ontology"]
        for field in BOOLEAN_FIELDS:
            row[field] = parse_bool(row.get(field))
        by_ontology[row["ontology"]].append(row)
    if len(by_ontology) != 592:
        raise SystemExit(f"expected 592 ontologies, found {len(by_ontology)}")
    expected_arm_set = set(expected_arms)

    corrections: list[dict] = []
    for ontology, ontology_rows in sorted(by_ontology.items()):
        observed_arms = [row["arm"] for row in ontology_rows]
        if observed_arms != expected_arms:
            raise SystemExit(f"ordered procedure-contract mismatch for {ontology}")
        indexed = {row["arm"]: row for row in ontology_rows}
        if set(indexed) != expected_arm_set:
            raise SystemExit(f"procedure-set mismatch for {ontology}")
        reference = indexed["konclude"]
        for row in ontology_rows:
            before = {field: row.get(field) for field in CORRECTNESS_FIELDS}
            classify_correctness(row, reference)
            apply_retained_targeted_adjudication(row)
            after = {field: row.get(field) for field in CORRECTNESS_FIELDS}
            if before != after:
                corrections.append(
                    {
                        "ontology": ontology,
                        "arm": row["arm"],
                        "old_sound": before["sound"],
                        "new_sound": after["sound"],
                        "old_complete": before["complete"],
                        "new_complete": after["complete"],
                        "old_solved": bool_text(before["solved"]),
                        "new_solved": bool_text(after["solved"]),
                        "old_correctness_basis": before["correctness_basis"],
                        "new_correctness_basis": after["correctness_basis"],
                        "fulliri_taxonomy_sha256": row.get(
                            "fulliri_taxonomy_sha256", ""
                        ),
                    }
                )

    # The generic scorer must repair the exact eight KM-auto rows that exposed
    # the v1 bug.  This invariant turns a future regression into a hard failure.
    expected_repaired_auto = {
        "ore_ont_443.owl",
        "ore_ont_3524.owl",
        "ore_ont_6720.owl",
        "ore_ont_7052.owl",
        "ore_ont_8941.owl",
        "ore_ont_13912.owl",
        "ore_ont_15288.owl",
        "ore_ont_15703.owl",
    }
    repaired_auto = {
        row["ontology"]
        for row in rows
        if row["arm"] == "km_route_auto"
        and row["ontology"] in expected_repaired_auto
        and row.get("sound") == row.get("complete") == "yes"
    }
    if repaired_auto != expected_repaired_auto:
        raise SystemExit(
            "v2 scorer failed its eight-ontology regression invariant: "
            f"{sorted(expected_repaired_auto - repaired_auto)}"
        )

    with args.wide.open(newline="", encoding="utf-8") as handle:
        wide_reader = csv.DictReader(handle, delimiter="\t")
        wide_fields = list(wide_reader.fieldnames or [])
        wide_rows = list(wide_reader)
    if len(wide_rows) != 592:
        raise SystemExit(f"expected 592 wide rows, found {len(wide_rows)}")
    documented_arm = {
        row["ontology"]: row.get("panel_documented_route_arm", "")
        for row in wide_rows
    }

    indexed_all = {
        ontology: {row["arm"]: row for row in ontology_rows}
        for ontology, ontology_rows in by_ontology.items()
    }
    documented_rows: list[dict] = []
    best_rows: list[dict] = []
    documented_by_ontology: dict[str, dict] = {}
    best_by_ontology: dict[str, dict | None] = {}
    for ontology in sorted(by_ontology):
        arm = documented_arm[ontology]
        documented = (
            indexed_all[ontology][arm]
            if arm
            else {
                "status": "no_claim",
                "sound": "not_applicable",
                "complete": "no",
                "solved": False,
            }
        )
        documented_rows.append(documented)
        documented_by_ontology[ontology] = documented
        eligible = [
            row
            for row in by_ontology[ontology]
            if row.get("family") in {"km_route", "km_documented_solution_route"}
            and row.get("status") == "ok"
            and row.get("solved") is True
        ]
        best = min(eligible, key=lambda row: float(row["wall_s"])) if eligible else None
        best_by_ontology[ontology] = best
        best_rows.append(
            best
            if best is not None
            else {
                "status": "no_claim",
                "sound": "not_applicable",
                "complete": "no",
                "solved": False,
            }
        )

    headline = [
        summarize("km_documented_selected", documented_rows),
        summarize("km_best_current_route", best_rows),
    ]
    for label, arm in STANDARD_ARMS.items():
        headline.append(
            summarize(label, [indexed_all[o][arm] for o in sorted(indexed_all)])
        )
    per_arm = [
        summarize(arm, [indexed_all[o][arm] for o in sorted(indexed_all)])
        for arm in expected_arms
    ]

    # Publish a corrected 592-row table as a new artifact.  The frozen v1 wide
    # table remains untouched; all measurement and provenance fields are copied
    # verbatim, while its derived panel correctness views are synchronized with
    # the same rows used for the v2 long table and headline.
    wide_arm_prefixes = {
        "panel_km_auto": "km_route_auto",
        "panel_konclude": "konclude",
        "panel_hermit": "hermit",
        "panel_elk": "elk",
        "panel_rustdl": "rustdl_complete",
        "panel_sequoia": "sequoia_strict",
    }
    for wide in wide_rows:
        ontology = wide["ontology"]
        indexed = indexed_all[ontology]
        for prefix, arm in wide_arm_prefixes.items():
            source = indexed[arm]
            wide[f"{prefix}_sound"] = source["sound"]
            wide[f"{prefix}_complete"] = source["complete"]
            wide[f"{prefix}_correctness_basis"] = source["correctness_basis"]

        selected_arm = documented_arm[ontology]
        if selected_arm:
            selected = documented_by_ontology[ontology]
            wide["panel_documented_route_sound"] = selected["sound"]
            wide["panel_documented_route_complete"] = selected["complete"]
            wide["panel_documented_route_correctness_basis"] = selected[
                "correctness_basis"
            ]

        best = best_by_ontology[ontology]
        if best is None:
            wide["panel_best_km_arm"] = ""
            wide["panel_best_km_wall_s"] = ""
            wide["panel_best_km_peak_mb"] = ""
        else:
            wide["panel_best_km_arm"] = best["arm"]
            wide["panel_best_km_wall_s"] = best["wall_s"]
            wide["panel_best_km_peak_mb"] = best["peak_mb"]

        compact = json.loads(wide["panel_all_procedures_json"])
        if {entry["arm"] for entry in compact} != set(indexed):
            raise SystemExit(f"wide compact procedure-set mismatch for {ontology}")
        for entry in compact:
            source = indexed[entry["arm"]]
            entry["sound"] = source["sound"]
            entry["complete"] = source["complete"]
            entry["solved"] = source["solved"]
            entry["correctness_basis"] = source["correctness_basis"]
            entry["fulliri_verdict"] = source["fulliri_verdict"]
        wide["panel_all_procedures_json"] = json.dumps(compact, separators=(",", ":"))

    # Recompute the retained optimization comparisons with v2 solve labels.
    # Pair definitions come from the frozen artifact, so this cannot silently
    # add, remove, or reorder an optimization comparison.
    optimization_v1_path = args.output_dir / "optimization-effects.tsv"
    with optimization_v1_path.open(newline="", encoding="utf-8") as handle:
        optimization_pairs = list(csv.DictReader(handle, delimiter="\t"))
    optimization_rows: list[dict] = []
    for old in optimization_pairs:
        optimized = [
            indexed_all[ontology][old["optimized_arm"]]
            for ontology in sorted(indexed_all)
        ]
        reference_rows = [
            indexed_all[ontology][old["reference_arm"]]
            for ontology in sorted(indexed_all)
        ]
        paired = [
            (new, reference)
            for new, reference in zip(optimized, reference_rows)
            if new.get("status") == reference.get("status") == "ok"
            and new.get("solved") is True
            and reference.get("solved") is True
        ]
        wall_delta = [
            float(new["wall_s"]) - float(reference["wall_s"])
            for new, reference in paired
        ]
        peak_delta = [
            float(new["peak_mb"]) - float(reference["peak_mb"])
            for new, reference in paired
        ]
        optimized_solved = sum(row.get("solved") is True for row in optimized)
        reference_solved = sum(row.get("solved") is True for row in reference_rows)
        optimization_rows.append(
            {
                "comparison_kind": old["comparison_kind"],
                "optimized_arm": old["optimized_arm"],
                "reference_arm": old["reference_arm"],
                "optimized_sound_complete": optimized_solved,
                "reference_sound_complete": reference_solved,
                "sound_complete_delta": optimized_solved - reference_solved,
                "paired_sound_complete": len(paired),
                "wall_mean_delta_s": round(statistics.mean(wall_delta), 4),
                "wall_median_delta_s": round(statistics.median(wall_delta), 4),
                "wall_faster": sum(delta < 0 for delta in wall_delta),
                "wall_equal": sum(delta == 0 for delta in wall_delta),
                "wall_slower": sum(delta > 0 for delta in wall_delta),
                "peak_mean_delta_mb": round(statistics.mean(peak_delta), 4),
                "peak_median_delta_mb": round(statistics.median(peak_delta), 4),
                "peak_lower": sum(delta < 0 for delta in peak_delta),
                "peak_equal": sum(delta == 0 for delta in peak_delta),
                "peak_higher": sum(delta > 0 for delta in peak_delta),
            }
        )

    for row in rows:
        row.pop("ont", None)
    long_path = args.output_dir / "full-panel-results.scoring-v2.tsv.gz"
    corrections_path = args.output_dir / "scoring-v2-corrections.tsv"
    headline_path = args.output_dir / "headline-summary.scoring-v2.tsv"
    summary_path = args.output_dir / "full-panel-summary.scoring-v2.tsv"
    wide_path = args.output_dir / "ontology-route-performance.scoring-v2.tsv"
    optimization_path = args.output_dir / "optimization-effects.scoring-v2.tsv"
    write_gzip_tsv(long_path, rows, fields)
    write_tsv(
        corrections_path,
        corrections,
        list(corrections[0]) if corrections else ["ontology", "arm"],
    )
    write_tsv(headline_path, headline, list(headline[0]))
    write_tsv(summary_path, per_arm, list(per_arm[0]))
    write_tsv(wide_path, wide_rows, wide_fields)
    write_tsv(optimization_path, optimization_rows, list(optimization_rows[0]))

    route_audit_path = args.output_dir / "route-coverage-audit.scoring-v2.json"
    if not route_audit_path.is_file():
        raise SystemExit(
            "missing mandatory historical route-coverage audit: "
            f"{route_audit_path}"
        )
    route_audit = json.loads(route_audit_path.read_text(encoding="utf-8"))
    if (
        route_audit.get("status") != "complete"
        or route_audit.get("accepted_rows") != 589
        or route_audit.get("missing_environment_count") != 0
    ):
        raise SystemExit("historical route-coverage audit did not pass")

    outputs = [
        long_path,
        corrections_path,
        headline_path,
        summary_path,
        wide_path,
        optimization_path,
        route_audit_path,
    ]
    semantic_corrections = sum(
        correction["old_sound"] != correction["new_sound"]
        or correction["old_complete"] != correction["new_complete"]
        or correction["old_solved"] != correction["new_solved"]
        for correction in corrections
    )
    scorer_path = Path(__file__).with_name("full_panel_correctness.py")
    try:
        scorer_display = str(scorer_path.resolve().relative_to(Path.cwd().resolve()))
    except ValueError:
        scorer_display = scorer_path.name
    receipt = {
        "schema_version": 2,
        "status": "rescored_without_reasoner_rerun",
        "scoring_semantics": (
            "shared inconsistency is semantic identity; audited collision-unsafe "
            "local-name projections use exact same-job full-IRI identity"
        ),
        "input": str(args.input),
        "input_sha256": sha256_file(args.input),
        "wide_input": str(args.wide),
        "wide_input_sha256": sha256_file(args.wide),
        "contract": str(contract_path),
        "contract_sha256": sha256_file(contract_path),
        "procedure_count": len(expected_arms),
        "scorer": scorer_display,
        "scorer_sha256": sha256_file(scorer_path),
        "driver_sha256": sha256_file(Path(__file__)),
        "row_count": len(rows),
        "correction_count": len(corrections),
        "semantic_correction_count": semantic_corrections,
        "basis_only_correction_count": len(corrections) - semantic_corrections,
        "historical_route_coverage": route_audit,
        "outputs": {path.name: sha256_file(path) for path in outputs},
        "headline": headline,
    }
    receipt_path = args.output_dir / "scoring-v2-receipt.json"
    receipt_path.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
