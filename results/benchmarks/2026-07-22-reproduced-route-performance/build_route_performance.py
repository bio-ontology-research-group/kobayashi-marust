#!/usr/bin/env python3
"""Build a source-pinned ORE route, correctness, and performance ledger."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
import math
from pathlib import Path
import statistics


EXPECTED_LEDGER_SHA256 = (
    "7db5b5b3c645cb2f37e515d215808ef3de499249c7a2d3fd22ec50771e64f354"
)
EXPECTED_BASELINE_MANIFEST_SHA256 = (
    "a3310200ba3ad26b19cddc0173df5be65541ff5246cfea9062325cb1f799b06f"
)
EXPECTED_STATES = {
    "not_a_documented_solve_claim": 3,
    "reproduced_adjudicated_inconsistent": 2,
    "reproduced_exact_full_iri": 579,
    "reproduced_exact_source_candidate_full_iri": 3,
    "reproduced_exact_source_historical_full_iri": 5,
}
EXPECTED_NONCLAIMS = {
    "ore_ont_10860.owl",
    "ore_ont_1194.owl",
    "ore_ont_4669.owl",
}
ADJUDICATED_INCONSISTENT = {
    "ore_ont_2669.owl",
    "ore_ont_15516.owl",
}
EMPTY_LOCAL_NAME_GOLD_FIX = "ore_ont_11745.owl"
MISSING_UNSAT_GOLD_FIX = "ore_ont_13503.owl"

BASELINE_ARMS = {
    "konclude": "konclude_w16",
    "hermit": "hermit",
    "elk": "elk",
}
EXPECTED_BASELINE_BINARY_SHA256 = {
    "konclude": "5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3",
    "hermit": "389a119fa7b168e4fbb291850bcff8b5d39e5c59e4da1abea03544ddb8c3ccab",
    "elk": "8340bc1421c28aa5f0affff3a5533ef3f24f6cf19b3df7bbe43e237f7633600c",
}
EXPECTED_RUNNER_SHA256 = (
    "3b1d2a878cae0e79f66de34fed4cd5c9dce1e457c958a5ce10d579217549c9d0"
)
EXPECTED_CANONICALIZER_SHA256 = (
    "2fc28764e34418ae3004f6dca7bb9bb6c6f763b022b0d356b80f896fa18173a2"
)
EXPECTED_JAVA_SHA256 = (
    "854f27091cbf804f7fa6bfb2d958210740eb55e6d21f59d931f95a354a1a0619"
)
EXPECTED_BASELINE_STATUS = {
    "konclude": {"error": 1, "memout": 2, "ok": 588, "timeout": 1},
    "hermit": {"error": 2, "ok": 556, "timeout": 33, "unsupported": 1},
    "elk": {"error": 2, "ok": 590},
}
EXPECTED_BASELINE_OK_METRICS = {
    "konclude": {
        "count": 588,
        "wall_mean": 2.129180612244898,
        "wall_median": 0.2641,
        "peak_mean": 738.2740476190477,
        "peak_median": 244.825,
    },
    "hermit": {
        "count": 556,
        "wall_mean": 12.952696223021583,
        "wall_median": 1.75905,
        "peak_mean": 1369.2545683453238,
        "peak_median": 741.1600000000001,
    },
    "elk": {
        "count": 590,
        "wall_mean": 1.9682403389830507,
        "wall_median": 0.82145,
        "peak_mean": 602.2810847457628,
        "peak_median": 347.225,
    },
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_json_sha256(value: object) -> str:
    payload = json.dumps(
        value, ensure_ascii=False, separators=(",", ":"), sort_keys=True
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def evidence_path(locator: str) -> Path:
    require(locator.startswith("ibex:/"), f"unsupported locator: {locator}")
    return Path(locator.removeprefix("ibex:"))


def same_number(left: object, right: object, tolerance: float = 1e-9) -> bool:
    try:
        return math.isclose(
            float(left), float(right), rel_tol=0, abs_tol=tolerance
        )
    except (TypeError, ValueError):
        return False


def route_name(row: dict[str, str]) -> str:
    requested = row["requested_route"]
    if requested and requested != "manual":
        return requested
    return (
        row["rebuilt_historical_route"]
        or row["historical_route"]
        or row["route_label"]
    )


def nearest_rank(values: list[float], percentile: float) -> float:
    ordered = sorted(values)
    rank = max(1, math.ceil(percentile * len(ordered)))
    return ordered[rank - 1]


def metrics(wall: list[float], peak: list[float]) -> dict[str, object]:
    require(len(wall) == len(peak) and wall, "empty or unpaired metrics")
    return {
        "count": len(wall),
        "wall_s": {
            "mean": statistics.fmean(wall),
            "median": statistics.median(wall),
            "p95_nearest_rank": nearest_rank(wall, 0.95),
        },
        "peak_mb": {
            "mean": statistics.fmean(peak),
            "median": statistics.median(peak),
            "p95_nearest_rank": nearest_rank(peak, 0.95),
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ledger", type=Path, required=True)
    parser.add_argument("--baseline-results", type=Path, required=True)
    parser.add_argument("--output-tsv", type=Path, required=True)
    parser.add_argument("--output-summary", type=Path, required=True)
    parser.add_argument("--output-receipt", type=Path, required=True)
    parser.add_argument("--slurm-job-id", required=True)
    parser.add_argument("--aggregation-driver-sha256", required=True)
    return parser.parse_args()


def load_baselines(
    root: Path, expected_ontologies: set[str]
) -> tuple[dict[str, dict[str, dict[str, object]]], list[dict[str, str]]]:
    require(root.is_dir() and not root.is_symlink(), "bad baseline result root")
    paths = sorted(root.glob("*.jsonl"), key=lambda path: path.name)
    require(len(paths) == 592, "baseline root must contain 592 JSONL files")
    require({path.name.removesuffix(".jsonl") for path in paths} == expected_ontologies,
            "baseline ontology set mismatch")

    manifest_digest = hashlib.sha256()
    manifest: list[dict[str, str]] = []
    by_ontology: dict[str, dict[str, dict[str, object]]] = {}
    statuses: dict[str, Counter[str]] = {
        reasoner: Counter() for reasoner in BASELINE_ARMS
    }
    ok_metrics: dict[str, dict[str, list[float]]] = {
        reasoner: {"wall": [], "peak": []} for reasoner in BASELINE_ARMS
    }

    for path in paths:
        require(path.is_file() and not path.is_symlink(), f"bad baseline file: {path}")
        digest = sha256(path)
        manifest_digest.update(path.name.encode("utf-8"))
        manifest_digest.update(b"\0")
        manifest_digest.update(digest.encode("ascii"))
        manifest_digest.update(b"\0")
        manifest.append(
            {"locator": f"ibex:{path}", "sha256": digest}
        )

        raw_rows = [
            json.loads(line)
            for line in path.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        require(len(raw_rows) == 28, f"baseline panel is not 28 rows: {path}")
        require(
            len({str(row.get("arm")) for row in raw_rows}) == 28,
            f"duplicate baseline arms: {path}",
        )
        ontology = path.name.removesuffix(".jsonl")
        require(
            {str(row.get("ont")) for row in raw_rows} == {ontology},
            f"baseline ontology identity mismatch: {path}",
        )
        rows_by_arm = {str(row["arm"]): row for row in raw_rows}
        selected: dict[str, dict[str, object]] = {}
        for reasoner, arm in BASELINE_ARMS.items():
            require(arm in rows_by_arm, f"missing {arm}: {path}")
            row = rows_by_arm[arm]
            require(
                row.get("binary_sha256")
                == EXPECTED_BASELINE_BINARY_SHA256[reasoner],
                f"{reasoner} binary mismatch: {path}",
            )
            require(
                row.get("runner_sha256") == EXPECTED_RUNNER_SHA256,
                f"runner mismatch: {path}",
            )
            require(
                row.get("canonicalizer_sha256")
                == EXPECTED_CANONICALIZER_SHA256,
                f"canonicalizer mismatch: {path}",
            )
            require(
                row.get("cpu_model")
                == "Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"
                and int(row.get("cpus", 0)) == 16,
                f"baseline hardware mismatch: {path}",
            )
            if reasoner in {"hermit", "elk"}:
                require(
                    row.get("runtime_sha256") == EXPECTED_JAVA_SHA256,
                    f"Java runtime mismatch: {path}",
                )
            else:
                require(
                    row.get("runtime_sha256") is None,
                    f"unexpected Konclude runtime: {path}",
                )
            status = str(row.get("status"))
            statuses[reasoner][status] += 1
            if status == "ok":
                ok_metrics[reasoner]["wall"].append(float(row["wall_s"]))
                ok_metrics[reasoner]["peak"].append(float(row["peak_mb"]))
            selected[reasoner] = row
        by_ontology[ontology] = selected

    require(
        manifest_digest.hexdigest() == EXPECTED_BASELINE_MANIFEST_SHA256,
        "unexpected baseline result manifest",
    )
    for reasoner in BASELINE_ARMS:
        require(
            dict(sorted(statuses[reasoner].items()))
            == EXPECTED_BASELINE_STATUS[reasoner],
            f"unexpected {reasoner} status counts",
        )
        expected = EXPECTED_BASELINE_OK_METRICS[reasoner]
        wall = ok_metrics[reasoner]["wall"]
        peak = ok_metrics[reasoner]["peak"]
        require(len(wall) == expected["count"], f"{reasoner} OK count")
        require(
            same_number(statistics.fmean(wall), expected["wall_mean"])
            and same_number(statistics.median(wall), expected["wall_median"])
            and same_number(statistics.fmean(peak), expected["peak_mean"])
            and same_number(statistics.median(peak), expected["peak_median"]),
            f"{reasoner} aggregate mismatch",
        )
    return by_ontology, manifest


def baseline_judgement(
    reasoner: str, ontology: str, row: dict[str, object]
) -> tuple[str, str, str]:
    status = str(row.get("status"))
    if status != "ok":
        return "not_applicable", "no", f"no_classification:{status}"

    # Later full-IRI and contradiction audits supersede the frozen local-name
    # comparator on these four ontologies.
    if ontology in ADJUDICATED_INCONSISTENT:
        if row.get("consistent") is False:
            return "yes", "yes", "adjudicated_inconsistent"
        if row.get("consistent") is True:
            return "yes", "no", "adjudicated_inconsistent_but_reported_consistent"
        return "unknown", "unknown", "adjudicated_inconsistent_no_consistency_answer"
    if ontology == EMPTY_LOCAL_NAME_GOLD_FIX:
        return "yes", "yes", "adjudicated_empty_local_name_gold_loader_fix"
    if ontology == MISSING_UNSAT_GOLD_FIX:
        if reasoner == "hermit":
            return "yes", "yes", "adjudicated_missing_unsatisfiable_class"
        return "yes", "no", "adjudicated_missing_unsatisfiable_class"

    if row.get("gold_kind") == "none":
        return "unknown", "unknown", "no_authoritative_oracle"
    verdict = str(row.get("verdict"))
    if verdict == "match":
        return "yes", "yes", "frozen_konclude_local_name_oracle"
    if verdict == "incomplete":
        return "yes", "no", "frozen_konclude_local_name_oracle"
    if verdict == "unsound":
        return "no", "yes", "frozen_konclude_local_name_oracle"
    if verdict == "both":
        return "no", "no", "frozen_konclude_local_name_oracle"
    if verdict == "consistency_mismatch":
        if row.get("consistent") is False:
            return "no", "yes", "frozen_konclude_local_name_oracle"
        return "yes", "no", "frozen_konclude_local_name_oracle"
    return "unknown", "unknown", f"unadjudicated_verdict:{verdict}"


def correctness_counts(
    rows: list[dict[str, object]], prefix: str
) -> dict[str, object]:
    sound = Counter(str(row[f"{prefix}_sound"]) for row in rows)
    complete = Counter(str(row[f"{prefix}_complete"]) for row in rows)
    joint = Counter(
        (
            str(row[f"{prefix}_sound"]),
            str(row[f"{prefix}_complete"]),
        )
        for row in rows
    )
    return {
        "sound": dict(sorted(sound.items())),
        "complete": dict(sorted(complete.items())),
        "sound_and_complete": joint[("yes", "yes")],
        "joint": {
            f"sound={sound_value},complete={complete_value}": count
            for (sound_value, complete_value), count in sorted(joint.items())
        },
    }


def baseline_metrics(
    rows: list[dict[str, object]], prefix: str
) -> dict[str, object]:
    successful = [row for row in rows if row[f"{prefix}_status"] == "ok"]
    return metrics(
        [float(row[f"{prefix}_wall_s"]) for row in successful],
        [float(row[f"{prefix}_peak_mb"]) for row in successful],
    )


def main() -> int:
    args = parse_args()
    require(
        sha256(args.ledger) == EXPECTED_LEDGER_SHA256,
        "unexpected reproduced-route ledger SHA-256",
    )
    with args.ledger.open(newline="", encoding="utf-8") as handle:
        ledger_rows = list(csv.DictReader(handle, delimiter="\t"))
    require(len(ledger_rows) == 592, "ledger must contain 592 rows")
    ontology_set = {row["ontology"] for row in ledger_rows}
    require(len(ontology_set) == 592, "ontology identifiers must be unique")
    require(
        dict(Counter(row["current_state"] for row in ledger_rows))
        == EXPECTED_STATES,
        "unexpected ledger state counts",
    )
    baselines, baseline_manifest = load_baselines(
        args.baseline_results, ontology_set
    )

    output_rows: list[dict[str, object]] = []
    route_evidence_manifest: list[dict[str, str]] = []
    km_all_wall: list[float] = []
    km_all_peak: list[float] = []
    km_paired_wall: list[float] = []
    km_paired_peak: list[float] = []
    konclude_paired_wall: list[float] = []
    konclude_paired_peak: list[float] = []

    for row in ledger_rows:
        ontology = row["ontology"]
        reproduced = row["current_state"].startswith("reproduced_")
        baseline = baselines[ontology]

        common: dict[str, object] = {
            "ontology": ontology,
            "km_state": (
                row["current_state"]
                if reproduced
                else "not_currently_verified_solved"
            ),
            "km_route": "",
            "km_observed_route_identity": "",
            "km_route_environment": "",
            "km_command_json": "",
            "km_status": "",
            "km_wall_s": "",
            "km_peak_mb": "",
            "km_sound": "",
            "km_complete": "",
            "km_correctness_basis": "",
            "km_source_revision": "",
            "km_source_manifest_sha256": "",
            "km_build_receipt_sha256": "",
            "km_binary_sha256": "",
            "km_taxonomy_sha256": "",
            "km_evidence_locator": "",
            "km_evidence_sha256": "",
        }

        accepted_record: dict[str, object] | None = None
        if reproduced:
            path = evidence_path(row["evidence_locator"])
            require(path.is_file() and not path.is_symlink(), f"bad evidence: {path}")
            record_sha = sha256(path)
            require(record_sha == row["evidence_sha256"], f"evidence hash: {path}")
            accepted_record = json.loads(path.read_text(encoding="utf-8"))
            require(accepted_record.get("ontology") == ontology, "ontology mismatch")
            require(
                accepted_record.get("ontology_sha256") == row["ontology_sha256"],
                f"ontology SHA-256 mismatch: {ontology}",
            )
            km_run = accepted_record.get("km_run") or {}
            require(km_run.get("status") == "ok", f"KM run status: {ontology}")
            require(
                km_run.get("binary_sha256") == row["binary_sha256"],
                f"KM binary mismatch: {ontology}",
            )
            require(
                same_number(km_run.get("wall_s"), row["wall_s"])
                and same_number(km_run.get("peak_mb"), row["peak_mb"]),
                f"KM measurement mismatch: {ontology}",
            )
            require(
                same_number(km_run.get("timeout_s"), 240)
                and same_number(km_run.get("memory_limit_mb"), 20480)
                and int(km_run.get("cpus", 0)) == 16,
                f"KM limits mismatch: {ontology}",
            )
            km_wall = float(row["wall_s"])
            km_peak = float(row["peak_mb"])
            km_all_wall.append(km_wall)
            km_all_peak.append(km_peak)
            basis = (
                "adjudicated_inconsistent"
                if ontology in ADJUDICATED_INCONSISTENT
                else "exact_current_full_iri_konclude"
            )
            common.update(
                {
                    "km_route": route_name(row),
                    "km_observed_route_identity": row["observed_route_identity"],
                    "km_route_environment": row["route_environment"],
                    "km_command_json": row["command_json"],
                    "km_status": "ok",
                    "km_wall_s": f"{km_wall:.4f}",
                    "km_peak_mb": f"{km_peak:.2f}",
                    "km_sound": "yes",
                    "km_complete": "yes",
                    "km_correctness_basis": basis,
                    "km_source_revision": row["source_revision"],
                    "km_source_manifest_sha256": row["source_manifest_sha256"],
                    "km_build_receipt_sha256": row["build_receipt_sha256"],
                    "km_binary_sha256": row["binary_sha256"],
                    "km_taxonomy_sha256": row["km_taxonomy_sha256"],
                    "km_evidence_locator": row["evidence_locator"],
                    "km_evidence_sha256": row["evidence_sha256"],
                }
            )
            route_evidence_manifest.append(
                {"locator": row["evidence_locator"], "sha256": record_sha}
            )
        elif ontology == "ore_ont_4669.owl":
            common.update(
                {
                    "km_status": "completed_incorrect",
                    "km_sound": "no",
                    "km_complete": "unknown",
                    "km_correctness_basis": "targeted_satisfiability_counterexamples",
                }
            )
        elif ontology == "ore_ont_10860.owl":
            common.update(
                {
                    "km_status": "unsupported",
                    "km_sound": "not_applicable",
                    "km_complete": "no",
                    "km_correctness_basis": "unsupported_dl_safe_rule_atoms",
                }
            )
        elif ontology == "ore_ont_1194.owl":
            common.update(
                {
                    "km_status": "memout",
                    "km_sound": "not_applicable",
                    "km_complete": "no",
                    "km_correctness_basis": "no_complete_route_within_20_gib",
                }
            )
        else:
            raise RuntimeError(f"unexpected nonclaim: {ontology}")

        # The 587 exact accepted records carry a contemporaneous full-IRI
        # Konclude run. The other five rows use the frozen matrix measurement.
        if reproduced and row["reference_kind"] == "konclude_full_ontology":
            require(accepted_record is not None, "accepted record vanished")
            konclude = accepted_record.get("reference_run") or {}
            require(konclude.get("status") == "ok", f"Konclude run: {ontology}")
            require(
                konclude.get("binary_sha256") == row["reference_binary_sha256"],
                f"Konclude binary mismatch: {ontology}",
            )
            require(
                konclude.get("ontology_sha256") == row["ontology_sha256"],
                f"Konclude ontology mismatch: {ontology}",
            )
            require(
                same_number(konclude.get("timeout_s"), 240)
                and same_number(konclude.get("memory_limit_mb"), 20480),
                f"Konclude limits mismatch: {ontology}",
            )
            kon_wall = float(konclude["wall_s"])
            kon_peak = float(konclude["peak_mb"])
            km_paired_wall.append(float(common["km_wall_s"]))
            km_paired_peak.append(float(common["km_peak_mb"]))
            konclude_paired_wall.append(kon_wall)
            konclude_paired_peak.append(kon_peak)
            common.update(
                {
                    "konclude_status": "ok",
                    "konclude_wall_s": f"{kon_wall:.4f}",
                    "konclude_peak_mb": f"{kon_peak:.2f}",
                    "konclude_sound": "yes",
                    "konclude_complete": "yes",
                    "konclude_correctness_basis": "current_full_iri_reference",
                    "konclude_binary_sha256": konclude["binary_sha256"],
                    "konclude_signature_sha256": row["reference_taxonomy_sha256"],
                    "konclude_measurement_set": "current_paired_full_iri",
                    "konclude_evidence_locator": row["evidence_locator"],
                    "konclude_evidence_sha256": row["evidence_sha256"],
                    "km_over_konclude_wall_ratio": f"{float(common['km_wall_s']) / kon_wall:.6f}",
                    "km_over_konclude_peak_ratio": f"{float(common['km_peak_mb']) / kon_peak:.6f}",
                }
            )
        else:
            konclude = baseline["konclude"]
            sound, complete, basis = baseline_judgement(
                "konclude", ontology, konclude
            )
            baseline_path = args.baseline_results / f"{ontology}.jsonl"
            common.update(
                {
                    "konclude_status": str(konclude["status"]),
                    "konclude_wall_s": f"{float(konclude['wall_s']):.4f}",
                    "konclude_peak_mb": f"{float(konclude['peak_mb']):.2f}",
                    "konclude_sound": sound,
                    "konclude_complete": complete,
                    "konclude_correctness_basis": basis,
                    "konclude_binary_sha256": konclude["binary_sha256"],
                    "konclude_signature_sha256": konclude.get("signature_sha256") or "",
                    "konclude_measurement_set": "frozen_repaired_matrix",
                    "konclude_evidence_locator": f"ibex:{baseline_path}",
                    "konclude_evidence_sha256": sha256(baseline_path),
                    "km_over_konclude_wall_ratio": "",
                    "km_over_konclude_peak_ratio": "",
                }
            )

        baseline_path = args.baseline_results / f"{ontology}.jsonl"
        baseline_digest = sha256(baseline_path)
        for reasoner in ("hermit", "elk"):
            measured = baseline[reasoner]
            sound, complete, basis = baseline_judgement(
                reasoner, ontology, measured
            )
            common.update(
                {
                    f"{reasoner}_status": str(measured["status"]),
                    f"{reasoner}_wall_s": f"{float(measured['wall_s']):.4f}",
                    f"{reasoner}_peak_mb": f"{float(measured['peak_mb']):.2f}",
                    f"{reasoner}_sound": sound,
                    f"{reasoner}_complete": complete,
                    f"{reasoner}_correctness_basis": basis,
                    f"{reasoner}_binary_sha256": measured["binary_sha256"],
                    f"{reasoner}_signature_sha256": measured.get("signature_sha256") or "",
                }
            )
        common.update(
            {
                "external_baseline_evidence_locator": f"ibex:{baseline_path}",
                "external_baseline_evidence_sha256": baseline_digest,
            }
        )
        output_rows.append(common)

    nonclaims = {
        row["ontology"]
        for row in output_rows
        if row["km_state"] == "not_currently_verified_solved"
    }
    require(nonclaims == EXPECTED_NONCLAIMS, "unexpected nonclaim set")
    require(len(km_all_wall) == 589, "expected 589 KM measurements")
    require(len(konclude_paired_wall) == 587, "expected 587 paired Konclude rows")

    args.output_tsv.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = list(output_rows[0])
    with args.output_tsv.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fieldnames, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(output_rows)

    correctness = {
        reasoner: correctness_counts(output_rows, reasoner)
        for reasoner in ("km", "konclude", "hermit", "elk")
    }
    require(correctness["km"]["sound_and_complete"] == 589, "KM correctness count")
    require(
        correctness["konclude"]["sound_and_complete"] == 587,
        "Konclude correctness count",
    )
    require(
        correctness["hermit"]["sound_and_complete"] == 551,
        "HermiT correctness count",
    )
    require(correctness["elk"]["sound_and_complete"] == 531, "ELK correctness count")

    table_sha = sha256(args.output_tsv)
    route_manifest_sha = canonical_json_sha256(route_evidence_manifest)
    baseline_manifest_sha = canonical_json_sha256(baseline_manifest)
    summary = {
        "schema_version": 2,
        "status": "verified_route_correctness_performance",
        "slurm_job_id": args.slurm_job_id,
        "aggregation_driver_sha256": args.aggregation_driver_sha256,
        "source_ledger_sha256": EXPECTED_LEDGER_SHA256,
        "baseline_result_manifest_sha256": EXPECTED_BASELINE_MANIFEST_SHA256,
        "table_sha256": table_sha,
        "rows": 592,
        "reproduced": 589,
        "exact_full_iri": 587,
        "adjudicated_inconsistent": 2,
        "nonclaims": sorted(nonclaims),
        "route_evidence_record_count": len(route_evidence_manifest),
        "route_evidence_record_manifest_sha256": route_manifest_sha,
        "baseline_evidence_record_count": len(baseline_manifest),
        "baseline_evidence_record_manifest_sha256": baseline_manifest_sha,
        "metric_definition": {
            "wall_s": "process-group elapsed wall clock",
            "peak_mb": "maximum sampled process-group RSS in MiB, maxed with GNU time direct-child peak",
            "aggregate_population": "rows whose reasoner status is ok",
            "p95": "nearest-rank percentile",
        },
        "correctness_definition": {
            "scope": "empirical named-class taxonomy relative to the cited full-IRI reference, frozen local-name oracle, or explicit adjudication",
            "values": {
                "yes": "the evidence establishes the property",
                "no": "the evidence refutes the property",
                "unknown": "a result exists but the available evidence does not decide the property",
                "not_applicable": "no classification answer exists to assess for soundness",
            },
            "timeout_or_failure": "sound=not_applicable and complete=no",
        },
        "correctness": correctness,
        "km_all_reproduced": metrics(km_all_wall, km_all_peak),
        "paired_exact_full_iri": {
            "count": 587,
            "km": metrics(km_paired_wall, km_paired_peak),
            "konclude": metrics(konclude_paired_wall, konclude_paired_peak),
        },
        "frozen_repaired_external_baselines": {
            "konclude": baseline_metrics(
                [
                    {
                        "konclude_status": baselines[row["ontology"]]["konclude"]["status"],
                        "konclude_wall_s": baselines[row["ontology"]]["konclude"]["wall_s"],
                        "konclude_peak_mb": baselines[row["ontology"]]["konclude"]["peak_mb"],
                    }
                    for row in output_rows
                ],
                "konclude",
            ),
            "hermit": baseline_metrics(output_rows, "hermit"),
            "elk": baseline_metrics(output_rows, "elk"),
        },
        "notes": [
            "KM metrics use the one accepted source-bound route per reproduced ontology; they are not per-ontology oracle minima.",
            "The paired KM/Konclude comparison uses contemporaneous full-IRI runs for the same 587 ontologies.",
            "HermiT and ELK measurements use the repaired frozen matrix on the same CPU model and limits, but not the same Slurm job as the accepted KM routes.",
            "The repaired raw matrix manifest supersedes the pre-repair aggregate committed on 2026-07-16.",
        ],
    }
    args.output_summary.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    receipt = {
        "schema_version": 2,
        "status": "verified_route_correctness_performance_receipt",
        "slurm_job_id": args.slurm_job_id,
        "aggregation_driver_sha256": args.aggregation_driver_sha256,
        "builder_sha256": sha256(Path(__file__).resolve()),
        "source_ledger_sha256": EXPECTED_LEDGER_SHA256,
        "baseline_result_manifest_sha256": EXPECTED_BASELINE_MANIFEST_SHA256,
        "table_sha256": table_sha,
        "summary_sha256": sha256(args.output_summary),
        "route_evidence_record_count": len(route_evidence_manifest),
        "route_evidence_record_manifest_sha256": route_manifest_sha,
        "baseline_evidence_record_count": len(baseline_manifest),
        "baseline_evidence_record_manifest_sha256": baseline_manifest_sha,
        "rows": 592,
        "reproduced": 589,
        "exact_full_iri": 587,
        "adjudicated_inconsistent": 2,
        "nonclaims": sorted(nonclaims),
        "sound_and_complete": {
            reasoner: correctness[reasoner]["sound_and_complete"]
            for reasoner in ("km", "konclude", "hermit", "elk")
        },
    }
    args.output_receipt.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
