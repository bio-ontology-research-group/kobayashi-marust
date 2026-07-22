#!/usr/bin/env python3
"""Validate and aggregate the 592 x 66 reproduced ORE procedure panel."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import statistics

from full_panel_contract import (
    KM_REVISION,
    RUSTDL_REVISION,
    SEQUOIA_REVISION,
    OPTIMIZATION_ABLATIONS,
    OPTIMIZATION_STAGES,
    panel,
)


LONG_FIELDS = (
    "ontology",
    "arm",
    "family",
    "procedure_kind",
    "procedure_binary_key",
    "procedure_source_revision",
    "procedure_reverted_revision",
    "procedure_route",
    "procedure_documented_route",
    "status",
    "rc",
    "wall_s",
    "peak_mb",
    "limit_timeout_s",
    "limit_memcap_mib",
    "rss_sample_interval_ms",
    "sound",
    "complete",
    "solved",
    "verdict",
    "extra",
    "missing",
    "extra_unsat",
    "missing_unsat",
    "consistency_mismatch",
    "fulliri_verdict",
    "fulliri_fingerprint_status",
    "fulliri_identity_capable",
    "localname_identity_capable",
    "localname_canonicalization_status",
    "consistent",
    "subsumptions",
    "unsatisfiable",
    "fulliri_subsumptions",
    "fulliri_unsatisfiable",
    "fulliri_taxonomy_sha256",
    "fulliri_nodes_sha256",
    "fulliri_unsat_sha256",
    "binary_sha256",
    "binary_path",
    "runtime_sha256",
    "source_ontology_sha256",
    "gold_kind",
    "gold_basename",
    "gold_sha256",
    "signature_sha256",
    "stderr_sha256",
    "reported_incomplete",
    "checkpointed",
    "output_format",
    "expressivity",
    "fulliri_fingerprint_error",
    "requested_route",
    "command_json",
    "underlying_command_json",
    "explicit_environment_json",
    "procedure_contract_json",
    "correctness_basis",
    "pre_targeted_sound",
    "pre_targeted_complete",
    "pre_targeted_correctness_basis",
    "targeted_counterexample_count",
    "targeted_counterexamples_json",
    "targeted_adjudication_manifest_sha256",
    "host",
    "cpu_model",
    "cpus",
    "slurm_job_id",
    "slurm_array_task_id",
    "order_index",
    "runner_sha256",
    "runner_base_sha256",
    "canonicalizer_sha256",
    "watchdog_sha256",
    "benchmark_driver_sha256",
    "fingerprint_driver_sha256",
    "contract_sha256",
    "build_receipt_sha256",
    "fulliri_fingerprint_json",
    "fulliri_fingerprint_json_sha256",
)

STANDARD_ARMS = {
    "km_auto": "km_route_auto",
    "konclude": "konclude",
    "hermit": "hermit",
    "elk": "elk",
    "rustdl": "rustdl_complete",
    "sequoia": "sequoia_strict",
}

DOCUMENTED_ROUTE_ARMS = {
    "card_race": "km_solution_card_race",
    "htforce_race": "km_solution_htforce_race",
    "kpset_barrier": "km_solution_kpset_barrier",
    "legacy_tab_race": "km_solution_legacy_tab_race",
    "nomlink_default": "km_solution_nomlink_default",
    "shoq_race": "km_solution_shoq_race",
    "ht_rules": "km_solution_ht_rules_manual",
}

ADJUDICATION_4669_SOURCE_SHA256 = (
    "2b15dc9535ed50c4dc9eae05067df4e6525b69c7bf1913192715b79ad550b3eb"
)

FULLIRI_ONLY_ONTOLOGIES = {"ore_ont_3524.owl", "ore_ont_15703.owl"}
FULLIRI_ONLY_VERDICT = "localname_not_applicable_fulliri_only"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def named_digests_sha256(entries: dict[str, str]) -> str:
    digest = hashlib.sha256()
    for name, value in sorted(entries.items()):
        encoded = name.encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
        digest.update(bytes.fromhex(value))
    return digest.hexdigest()


def metric(values: list[float], operation) -> float | None:
    return round(operation(values), 4) if values else None


def percentile(values: list[float], fraction: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = max(0, math.ceil(len(ordered) * fraction) - 1)
    return round(ordered[index], 4)


def summarize_rows(
    arm: str,
    family: str,
    kind: str,
    rows: list[dict],
    procedure_contract: dict | None = None,
) -> dict:
    status = Counter(row.get("status") for row in rows)
    sound = Counter(row.get("sound") for row in rows)
    complete = Counter(row.get("complete") for row in rows)
    verdict = Counter(row.get("verdict") for row in rows)
    fulliri_verdict = Counter(row.get("fulliri_verdict") for row in rows)
    measured = [row for row in rows if row.get("status") == "ok"]
    attempted = [
        row
        for row in rows
        if row.get("wall_s") is not None and row.get("peak_mb") is not None
    ]
    walls = [float(row["wall_s"]) for row in measured]
    peaks = [float(row["peak_mb"]) for row in measured]
    attempt_walls = [float(row["wall_s"]) for row in attempted]
    attempt_peaks = [float(row["peak_mb"]) for row in attempted]
    return {
        "arm": arm,
        "family": family,
        "kind": kind,
        "n": len(rows),
        "sound_complete": sum(bool(row.get("solved")) for row in rows),
        "metric_rows": len(measured),
        "attempt_metric_rows": len(attempted),
        "fulliri_answers": sum(
            row.get("fulliri_fingerprint_status") == "ok" for row in rows
        ),
        "localname_match": verdict["match"],
        "fulliri_match": fulliri_verdict["match"],
        "localname_unsound": verdict["unsound"],
        "localname_incomplete": verdict["incomplete"],
        "localname_both": verdict["both"],
        "consistency_mismatch": verdict["consistency_mismatch"],
        "wall_mean_s": metric(walls, statistics.mean),
        "wall_median_s": metric(walls, statistics.median),
        "wall_p95_s": percentile(walls, 0.95),
        "peak_mean_mb": metric(peaks, statistics.mean),
        "peak_median_mb": metric(peaks, statistics.median),
        "peak_p95_mb": percentile(peaks, 0.95),
        "attempt_wall_mean_s": metric(attempt_walls, statistics.mean),
        "attempt_wall_median_s": metric(attempt_walls, statistics.median),
        "attempt_wall_p95_s": percentile(attempt_walls, 0.95),
        "attempt_peak_mean_mb": metric(attempt_peaks, statistics.mean),
        "attempt_peak_median_mb": metric(attempt_peaks, statistics.median),
        "attempt_peak_p95_mb": percentile(attempt_peaks, 0.95),
        "ok": status["ok"],
        "timeout": status["timeout"],
        "memout": status["memout"],
        "unsupported": status["unsupported"],
        "error": sum(
            count
            for name, count in status.items()
            if name not in {"ok", "timeout", "memout", "unsupported", "no_claim"}
        ),
        "no_claim": status["no_claim"],
        "sound_yes": sound["yes"],
        "sound_no": sound["no"],
        "sound_unknown": sound["unknown"],
        "sound_not_applicable": sound["not_applicable"],
        "complete_yes": complete["yes"],
        "complete_no": complete["no"],
        "complete_unknown": complete["unknown"],
        "procedure_contract": procedure_contract,
    }


def atomic_text(path: Path, text: str) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(text, encoding="utf-8")
    temporary.replace(path)


def documented_arm_for(row: dict) -> str:
    accepted_route = row.get("km_route", "")
    if accepted_route in DOCUMENTED_ROUTE_ARMS:
        return DOCUMENTED_ROUTE_ARMS[accepted_route]
    if accepted_route == "production_all" and row.get("km_route_environment", "").count(" ") > 0:
        return "km_solution_production_all_explicit"
    if accepted_route:
        return f"km_route_{accepted_route}"
    return ""


def load_hash_manifest(path: Path) -> dict[str, str]:
    entries = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        digest, name = line.split(None, 1)
        name = name.strip()
        if name in entries:
            raise SystemExit(f"duplicate manifest entry {name!r}: {path}")
        if len(digest) != 64 or any(character not in "0123456789abcdef" for character in digest):
            raise SystemExit(f"invalid SHA-256 in {path}: {digest!r}")
        entries[name] = digest
    return entries


def validate_flat_manifest(path: Path, subdirectory: str = "") -> dict[str, str]:
    """Hash every file named by a flat manifest and return its entries."""

    entries = load_hash_manifest(path)
    root = path.parent / subdirectory
    for name, expected_sha in entries.items():
        if Path(name).name != name:
            raise SystemExit(f"non-flat manifest entry {name!r}: {path}")
        candidate = root / name
        if not candidate.is_file():
            raise SystemExit(f"manifest input is missing: {candidate}")
        if sha256_file(candidate) != expected_sha:
            raise SystemExit(f"manifest hash mismatch: {candidate}")
    return entries


def apply_4669_targeted_adjudication(
    by_ontology: dict[str, dict[str, dict]],
    run_root: Path,
    evidence_manifest: Path,
) -> list[dict]:
    evidence_root = evidence_manifest.parent.resolve(strict=True)
    evidence_entries = load_hash_manifest(evidence_manifest)
    evidence: dict[str, dict] = {}
    evidence_records: list[tuple[str, dict]] = []
    for name, expected_sha in evidence_entries.items():
        candidate = (evidence_root / name).resolve(strict=True)
        try:
            candidate.relative_to(evidence_root)
        except ValueError as error:
            raise SystemExit(f"4669 evidence escapes its root: {name}") from error
        if sha256_file(candidate) != expected_sha:
            raise SystemExit(f"4669 evidence hash mismatch: {candidate}")
        record = json.loads(candidate.read_text(encoding="utf-8"))
        evidence_records.append((name, record))
        if record.get("status") == "ok" and record.get("satisfiable") is True:
            iri = record.get("class")
            if not iri or iri in evidence:
                raise SystemExit(f"invalid or duplicate 4669 satisfiable witness: {iri}")
            evidence[iri] = {
                "path": name,
                "sha256": expected_sha,
                "slurm_job_id": record.get("slurm_job_id"),
            }
    if len(evidence_entries) != 67 or len(evidence) != 64:
        raise SystemExit(
            "4669 adjudication must contain 67 query records and 64 "
            f"successful satisfiable witnesses, found {len(evidence_entries)} and {len(evidence)}"
        )
    expected_groups = {
        "4669-satisfiability": 56,
        "4669-production-unsat-sample": 10,
        "4669-positive-control": 1,
    }
    observed_groups = Counter(name.split("/", 1)[0] for name, _ in evidence_records)
    if observed_groups != Counter(expected_groups):
        raise SystemExit(f"unexpected 4669 evidence groups: {observed_groups}")
    observed_jobs = Counter(
        record.get("slurm_array_job_id") for _, record in evidence_records
    )
    expected_jobs = Counter(
        {"49075466": 3, "49075584": 53, "49075857": 1, "49076590": 10}
    )
    if observed_jobs != expected_jobs:
        raise SystemExit(f"unexpected 4669 evidence jobs: {observed_jobs}")
    if Counter(record.get("status") for _, record in evidence_records) != Counter(
        {"ok": 64, "timeout": 3}
    ):
        raise SystemExit("unexpected 4669 evidence status distribution")

    source_hashes = {
        row.get("source_ontology_sha256")
        for row in by_ontology["ore_ont_4669.owl"].values()
    }
    if source_hashes != {ADJUDICATION_4669_SOURCE_SHA256}:
        raise SystemExit(
            "4669 panel source differs from the targeted adjudication source: "
            f"{source_hashes}"
        )

    manifest_sha = sha256_file(evidence_manifest)
    rows = []
    for arm, row in by_ontology["ore_ont_4669.owl"].items():
        counterexamples: list[str] = []
        if row.get("status") == "ok" and row.get("fulliri_fingerprint_status") == "ok":
            if row.get("consistent") is False:
                counterexamples = [sorted(evidence)[0]]
            else:
                unsat_path = (
                    run_root
                    / "fingerprints"
                    / "ore_ont_4669.owl"
                    / f"{arm}.unsat.txt.gz"
                )
                if not unsat_path.is_file():
                    raise SystemExit(f"missing 4669 UNSAT fingerprint: {unsat_path}")
                if sha256_file(unsat_path) != row.get("fulliri_unsat_sha256"):
                    raise SystemExit(f"4669 UNSAT fingerprint hash mismatch: {unsat_path}")
                with gzip.open(unsat_path, "rt", encoding="utf-8") as handle:
                    output_unsat = {line.rstrip("\n") for line in handle if line.strip()}
                counterexamples = sorted(output_unsat.intersection(evidence))
        row["pre_targeted_sound"] = row.get("sound")
        row["pre_targeted_complete"] = row.get("complete")
        row["pre_targeted_correctness_basis"] = row.get("correctness_basis")
        row["targeted_counterexample_count"] = len(counterexamples)
        row["targeted_counterexamples"] = counterexamples
        row["targeted_adjudication_manifest_sha256"] = manifest_sha
        if counterexamples:
            row["sound"] = "no"
            row["solved"] = False
            row["correctness_basis"] = "targeted_satisfiability_counterexample"
        rows.append(
            {
                "arm": arm,
                "status": row.get("status"),
                "fulliri_fingerprint_status": row.get("fulliri_fingerprint_status"),
                "consistent": row.get("consistent"),
                "sound": row.get("sound"),
                "complete": row.get("complete"),
                "correctness_basis": row.get("correctness_basis"),
                "counterexample_count": len(counterexamples),
                "counterexamples_json": json.dumps(counterexamples, separators=(",", ":")),
                "evidence_manifest_sha256": manifest_sha,
                "source_ontology_sha256": ADJUDICATION_4669_SOURCE_SHA256,
            }
        )
    return rows


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--run-root", type=Path, required=True)
    parser.add_argument("--ontology-list", type=Path, required=True)
    parser.add_argument("--existing-wide", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--array-driver-manifest", type=Path, required=True)
    parser.add_argument("--supplemental-driver-manifest", type=Path, required=True)
    parser.add_argument("--build-receipt", type=Path, required=True)
    parser.add_argument("--binary-manifest", type=Path, required=True)
    parser.add_argument("--ablation-patches-manifest", type=Path, required=True)
    parser.add_argument("--adjudication-4669-manifest", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    contract = panel()
    arms = [row["arm"] for row in contract]
    ontologies = [line.strip() for line in args.ontology_list.read_text().splitlines() if line.strip()]
    if len(ontologies) != 592:
        raise SystemExit(f"expected 592 ontologies, found {len(ontologies)}")

    rows: list[dict] = []
    by_ontology: dict[str, dict[str, dict]] = {}
    for ontology in ontologies:
        path = args.run_root / "results" / f"{ontology}.jsonl"
        if not path.is_file():
            raise SystemExit(f"missing result: {path}")
        ontology_rows = [json.loads(line) for line in path.read_text().splitlines() if line]
        observed = [row.get("arm") for row in ontology_rows]
        if observed != arms:
            raise SystemExit(f"arm contract mismatch: {path}")
        if any(row.get("ont") != ontology for row in ontology_rows):
            raise SystemExit(f"ontology mismatch: {path}")
        by_ontology[ontology] = {row["arm"]: row for row in ontology_rows}
        rows.extend(ontology_rows)
    if len(rows) != 592 * len(arms):
        raise AssertionError(len(rows))
    if {float(row.get("limit_timeout_s", -1)) for row in rows} != {240.0}:
        raise SystemExit("panel rows do not all record the 240 second limit")
    if {int(row.get("limit_memcap_mib", -1)) for row in rows} != {20480}:
        raise SystemExit("panel rows do not all record the 20 GiB limit")
    if {int(row.get("rss_sample_interval_ms", -1)) for row in rows} != {20}:
        raise SystemExit("panel rows do not all record the 20 ms RSS sampler")
    if {int(row.get("cpus", -1)) for row in rows} != {16}:
        raise SystemExit("panel rows do not all record the 16-CPU allocation")
    allowed_statuses = {"ok", "timeout", "memout", "unsupported", "error", "output_error"}
    unexpected_statuses = {row.get("status") for row in rows} - allowed_statuses
    if unexpected_statuses:
        raise SystemExit(f"unexpected panel statuses: {sorted(unexpected_statuses)}")
    if any(row.get("status") == "ok" and row.get("rc") != 0 for row in rows):
        raise SystemExit("at least one status=ok row has a nonzero return code")
    missing_fingerprints = [
        (row.get("ont"), row.get("arm"))
        for row in rows
        if row.get("status") == "ok"
        and row.get("fulliri_fingerprint_status") != "ok"
    ]
    if missing_fingerprints:
        raise SystemExit(
            "successful classifications without full-IRI fingerprints: "
            f"{missing_fingerprints[:10]}"
        )
    slurm_job_ids = set()
    for task_index, ontology in enumerate(ontologies):
        ontology_rows = by_ontology[ontology]
        if {str(row.get("slurm_array_task_id")) for row in ontology_rows.values()} != {
            str(task_index)
        }:
            raise SystemExit(f"Slurm task index mismatch for {ontology}")
        ontology_job_ids = {
            str(row.get("slurm_job_id")) for row in ontology_rows.values()
        }
        if len(ontology_job_ids) != 1 or "None" in ontology_job_ids:
            raise SystemExit(f"mixed Slurm job IDs for {ontology}: {ontology_job_ids}")
        slurm_job_ids.update(ontology_job_ids)
        if {int(row.get("order_index", -1)) for row in ontology_rows.values()} != set(
            range(len(arms))
        ):
            raise SystemExit(f"execution-order permutation mismatch for {ontology}")
        source_hashes = {
            row.get("source_ontology_sha256") for row in ontology_rows.values()
        }
        if len(source_hashes) != 1 or None in source_hashes or "" in source_hashes:
            raise SystemExit(f"mixed source ontology hashes for {ontology}")
        gold_identities = {
            (
                row.get("gold_kind"),
                row.get("gold_basename"),
                row.get("gold_sha256"),
            )
            for row in ontology_rows.values()
        }
        if len(gold_identities) != 1:
            raise SystemExit(f"mixed gold identities for {ontology}: {gold_identities}")
    if len(slurm_job_ids) != len(ontologies):
        raise SystemExit(
            f"expected one distinct Slurm job per ontology, found {len(slurm_job_ids)}"
        )
    for procedure in contract:
        arm_rows = [row for row in rows if row["arm"] == procedure["arm"]]
        if any(row.get("procedure_contract") != procedure for row in arm_rows):
            raise SystemExit(f"procedure metadata mismatch for {procedure['arm']}")
        for identity_field in ("binary_sha256", "runtime_sha256"):
            observed = {row.get(identity_field) for row in arm_rows}
            if len(observed) != 1:
                raise SystemExit(
                    f"mixed {identity_field} for {procedure['arm']}: "
                    f"{sorted(str(value) for value in observed)}"
                )
    invariant_files = (
        "build_receipt_sha256",
        "benchmark_driver_sha256",
        "fingerprint_driver_sha256",
        "contract_sha256",
        "canonicalizer_sha256",
        "watchdog_sha256",
    )
    for field in invariant_files:
        observed = {row.get(field) for row in rows}
        if len(observed) != 1 or None in observed or "" in observed:
            raise SystemExit(f"mixed or missing {field}: {sorted(str(x) for x in observed)}")
    expected_contract_sha = sha256_file(Path(__file__).with_name("full_panel_contract.py"))
    if {row["contract_sha256"] for row in rows} != {expected_contract_sha}:
        raise SystemExit("result contract hash differs from the aggregation contract")

    provenance_inputs = (
        args.array_driver_manifest,
        args.supplemental_driver_manifest,
        args.build_receipt,
        args.binary_manifest,
        args.ablation_patches_manifest,
        args.adjudication_4669_manifest,
    )
    for path in provenance_inputs:
        if not path.is_file():
            raise SystemExit(f"missing provenance input: {path}")
    if {row["build_receipt_sha256"] for row in rows} != {
        sha256_file(args.build_receipt)
    }:
        raise SystemExit("result build-receipt hash differs from the supplied receipt")
    driver_entries = validate_flat_manifest(args.array_driver_manifest)
    supplemental_entries = validate_flat_manifest(args.supplemental_driver_manifest)
    binary_entries = validate_flat_manifest(args.binary_manifest, "bin")
    patch_entries = validate_flat_manifest(args.ablation_patches_manifest, "patches")

    supplemental_extras = {
        "full_panel_run_one_fulliri_only.py",
        "ibex_full_panel_giant_array.sbatch",
    }
    if set(supplemental_entries) != set(driver_entries) | supplemental_extras:
        raise SystemExit(
            "supplemental driver manifest differs from the primary driver plus "
            f"the two declared files: {sorted(set(supplemental_entries) ^ (set(driver_entries) | supplemental_extras))}"
        )
    for name, digest in driver_entries.items():
        if supplemental_entries.get(name) != digest:
            raise SystemExit(f"supplemental driver changed frozen primary input: {name}")

    primary_runner_sha = driver_entries["full_panel_run_one.py"]
    supplemental_runner_sha = supplemental_entries[
        "full_panel_run_one_fulliri_only.py"
    ]
    for row in rows:
        if row["ont"] in FULLIRI_ONLY_ONTOLOGIES:
            if row.get("runner_sha256") != supplemental_runner_sha:
                raise SystemExit(
                    f"supplemental runner mismatch for {(row['ont'], row['arm'])}"
                )
            if row.get("runner_base_sha256") != primary_runner_sha:
                raise SystemExit(
                    f"supplemental base-runner mismatch for {(row['ont'], row['arm'])}"
                )
            if row.get("localname_identity_capable") is not False:
                raise SystemExit(
                    f"supplemental local-name capability mismatch for {(row['ont'], row['arm'])}"
                )
            expected_projection_status = (
                "skipped_noninjective_projection"
                if row.get("status") == "ok"
                else "not_applicable_no_answer"
            )
            if row.get("localname_canonicalization_status") != expected_projection_status:
                raise SystemExit(
                    f"supplemental projection status mismatch for {(row['ont'], row['arm'])}"
                )
            if row.get("status") == "ok" and row.get("verdict") != FULLIRI_ONLY_VERDICT:
                raise SystemExit(
                    f"successful supplemental verdict mismatch for {(row['ont'], row['arm'])}"
                )
            if row.get("status") == "ok" and row.get("signature_sha256") is not None:
                raise SystemExit(
                    f"supplemental row unexpectedly has a local-name signature: {(row['ont'], row['arm'])}"
                )
        elif row.get("runner_sha256") != primary_runner_sha:
            raise SystemExit(f"primary runner mismatch for {(row['ont'], row['arm'])}")

    receipt = json.loads(args.build_receipt.read_text(encoding="utf-8"))
    receipt_binaries = {
        name: metadata.get("sha256")
        for name, metadata in receipt.get("binaries", {}).items()
    }
    expected_revisions = {
        "km_revision": KM_REVISION,
        "rustdl_revision": RUSTDL_REVISION,
        "sequoia_revision": SEQUOIA_REVISION,
    }
    for key, expected_revision in expected_revisions.items():
        if receipt.get(key) != expected_revision:
            raise SystemExit(
                f"build receipt {key}={receipt.get(key)!r}, expected {expected_revision}"
            )
    if receipt_binaries != binary_entries:
        raise SystemExit("binary manifest does not exactly match the build receipt")

    expected_km_variants: dict[str, tuple[str, str, str]] = {}
    for procedure in contract:
        if procedure["kind"] != "km":
            continue
        key = procedure["binary_key"]
        if procedure["family"] == "km_optimization_stage":
            variant = "chronological-optimization-stage"
        elif procedure["family"] == "km_optimization_ablation":
            variant = f"current-main-minus-{procedure['reverted_revision']}"
        else:
            variant = "current-main"
        expected = (
            procedure["source_revision"],
            variant,
            binary_entries[f"km-{key}"],
        )
        previous = expected_km_variants.setdefault(key, expected)
        if previous != expected:
            raise SystemExit(f"inconsistent binary contract for KM key {key}")

    variant_receipt_dir = args.build_receipt.parent / "receipts"
    variant_receipt_hashes: dict[str, str] = {}
    for key, (source_revision, variant, binary_sha) in expected_km_variants.items():
        path = variant_receipt_dir / f"km-{key}.json"
        if not path.is_file():
            raise SystemExit(f"missing KM variant build receipt: {path}")
        metadata = json.loads(path.read_text(encoding="utf-8"))
        expected_metadata = {
            "key": key,
            "source_revision": source_revision,
            "variant": variant,
            "binary_sha256": binary_sha,
        }
        for field, expected_value in expected_metadata.items():
            if metadata.get(field) != expected_value:
                raise SystemExit(
                    f"KM variant receipt mismatch {path.name} {field}: "
                    f"{metadata.get(field)!r} != {expected_value!r}"
                )
        variant_receipt_hashes[path.name] = sha256_file(path)
    expected_patch_names = {
        f"ablate-{revision[:12]}.patch"
        for _arm, revision in OPTIMIZATION_ABLATIONS
    }
    if set(patch_entries) != expected_patch_names:
        raise SystemExit(
            "ablation-patch manifest differs from the frozen ablation contract: "
            f"{sorted(set(patch_entries) ^ expected_patch_names)}"
        )
    build_script = Path(receipt.get("build_script", ""))
    if not build_script.is_file() or sha256_file(build_script) != receipt.get(
        "build_script_sha256"
    ):
        raise SystemExit("build script is missing or differs from the build receipt")

    expected_driver_entries = {
        "run_full_panel_ontology.py": rows[0]["benchmark_driver_sha256"],
        "full_panel_fingerprint.py": rows[0]["fingerprint_driver_sha256"],
        "full_panel_contract.py": rows[0]["contract_sha256"],
        "full_panel_run_one.py": rows[0]["runner_sha256"],
        "ore_canon.py": rows[0]["canonicalizer_sha256"],
        "tree_watchdog.py": rows[0]["watchdog_sha256"],
    }
    for name, digest in expected_driver_entries.items():
        if driver_entries.get(name) != digest:
            raise SystemExit(f"array-driver manifest mismatch for {name}")

    for procedure in contract:
        arm_rows = [row for row in rows if row["arm"] == procedure["arm"]]
        kind = procedure["kind"]
        if kind == "km":
            binary_name = f"km-{procedure['binary_key']}"
            expected_binary_sha = binary_entries[binary_name]
            if {row.get("binary_sha256") for row in arm_rows} != {
                expected_binary_sha
            }:
                raise SystemExit(f"build-manifest binary mismatch for {procedure['arm']}")
            expected_environment = (
                sorted(procedure["environment"])
                if procedure["family"] == "km_documented_solution_route"
                else [f"KM_ROUTE={procedure['route']}"]
            )
            if any(
                row.get("explicit_environment") != expected_environment
                for row in arm_rows
            ):
                raise SystemExit(f"KM environment mismatch for {procedure['arm']}")
            expected_route = next(
                value.split("=", 1)[1]
                for value in expected_environment
                if value.startswith("KM_ROUTE=")
            )
            if any(row.get("requested_route") != expected_route for row in arm_rows):
                raise SystemExit(f"requested KM route mismatch for {procedure['arm']}")
        elif kind == "hermit":
            if {row.get("binary_sha256") for row in arm_rows} != {
                binary_entries["FullIriHermitOracle.class"]
            }:
                raise SystemExit("HermiT oracle class differs from the build manifest")
        elif kind == "rustdl":
            if {row.get("binary_sha256") for row in arm_rows} != {
                driver_entries["rustdl_json_adapter.py"]
            }:
                raise SystemExit(f"RustDL adapter mismatch for {procedure['arm']}")
            if {row.get("runtime_sha256") for row in arm_rows} != {
                binary_entries["rustdl"]
            }:
                raise SystemExit(f"RustDL executable mismatch for {procedure['arm']}")
        elif kind == "sequoia":
            if {row.get("binary_sha256") for row in arm_rows} != {
                driver_entries["sequoia_json_adapter.py"]
            }:
                raise SystemExit(f"Sequoia adapter mismatch for {procedure['arm']}")

    adjudication_rows = apply_4669_targeted_adjudication(
        by_ontology, args.run_root, args.adjudication_4669_manifest
    )

    args.output_dir.mkdir(parents=True, exist_ok=True)
    contract_path = args.output_dir / "full-panel-contract.tsv"
    contract_fields = (
        "arm",
        "family",
        "kind",
        "binary_key",
        "source_revision",
        "reverted_revision",
        "route",
        "documented_route",
        "args_json",
        "environment_json",
        "standard_summary",
    )
    with contract_path.with_suffix(".tsv.tmp").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(
            handle, fieldnames=contract_fields, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        for procedure in contract:
            writer.writerow(
                {
                    **{key: procedure.get(key, "") for key in contract_fields},
                    "args_json": json.dumps(procedure.get("args", []), separators=(",", ":")),
                    "environment_json": json.dumps(
                        procedure.get("environment", []), separators=(",", ":")
                    ),
                }
            )
    contract_path.with_suffix(".tsv.tmp").replace(contract_path)

    identity_path = args.output_dir / "procedure-runtime-identities.tsv"
    identity_fields = (
        "arm",
        "family",
        "kind",
        "source_revision",
        "reverted_revision",
        "binary_path",
        "binary_sha256",
        "runtime_sha256",
        "requested_route",
        "output_format",
        "contract_args_json",
        "contract_environment_json",
        "actual_environment_json",
    )
    with identity_path.with_suffix(".tsv.tmp").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=identity_fields,
            delimiter="\t",
            lineterminator="\n",
        )
        writer.writeheader()
        for procedure in contract:
            sample = by_ontology[ontologies[0]][procedure["arm"]]
            writer.writerow(
                {
                    "arm": procedure["arm"],
                    "family": procedure["family"],
                    "kind": procedure["kind"],
                    "source_revision": procedure.get("source_revision"),
                    "reverted_revision": procedure.get("reverted_revision"),
                    "binary_path": sample.get("binary_path"),
                    "binary_sha256": sample.get("binary_sha256"),
                    "runtime_sha256": sample.get("runtime_sha256"),
                    "requested_route": sample.get("requested_route"),
                    "output_format": sample.get("output_format"),
                    "contract_args_json": json.dumps(
                        procedure.get("args", []), separators=(",", ":")
                    ),
                    "contract_environment_json": json.dumps(
                        procedure.get("environment", []), separators=(",", ":")
                    ),
                    "actual_environment_json": json.dumps(
                        sample.get("explicit_environment"), separators=(",", ":")
                    ),
                }
            )
    identity_path.with_suffix(".tsv.tmp").replace(identity_path)

    long_path = args.output_dir / "full-panel-results.tsv"
    with long_path.with_suffix(".tsv.tmp").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=LONG_FIELDS, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "ontology": row["ont"],
                    "arm": row["arm"],
                    "family": row.get("family"),
                    "procedure_kind": row.get("procedure_kind"),
                    "procedure_binary_key": row.get("procedure_contract", {}).get(
                        "binary_key"
                    ),
                    "procedure_source_revision": row.get("procedure_contract", {}).get(
                        "source_revision"
                    ),
                    "procedure_reverted_revision": row.get("procedure_contract", {}).get(
                        "reverted_revision"
                    ),
                    "procedure_route": row.get("procedure_contract", {}).get("route"),
                    "procedure_documented_route": row.get("procedure_contract", {}).get(
                        "documented_route"
                    ),
                    "status": row.get("status"),
                    "rc": row.get("rc"),
                    "wall_s": row.get("wall_s"),
                    "peak_mb": row.get("peak_mb"),
                    "limit_timeout_s": row.get("limit_timeout_s"),
                    "limit_memcap_mib": row.get("limit_memcap_mib"),
                    "rss_sample_interval_ms": row.get("rss_sample_interval_ms"),
                    "sound": row.get("sound"),
                    "complete": row.get("complete"),
                    "solved": row.get("solved"),
                    "verdict": row.get("verdict"),
                    "extra": row.get("extra"),
                    "missing": row.get("missing"),
                    "extra_unsat": row.get("extra_unsat"),
                    "missing_unsat": row.get("missing_unsat"),
                    "consistency_mismatch": row.get("consistency_mismatch"),
                    "fulliri_verdict": row.get("fulliri_verdict"),
                    "fulliri_fingerprint_status": row.get(
                        "fulliri_fingerprint_status"
                    ),
                    "fulliri_identity_capable": row.get("fulliri_identity_capable"),
                    "localname_identity_capable": row.get(
                        "localname_identity_capable"
                    ),
                    "localname_canonicalization_status": row.get(
                        "localname_canonicalization_status"
                    ),
                    "consistent": row.get("consistent"),
                    "subsumptions": row.get("subsumptions"),
                    "unsatisfiable": row.get("unsatisfiable"),
                    "fulliri_subsumptions": row.get("fulliri_subsumptions"),
                    "fulliri_unsatisfiable": row.get("fulliri_unsatisfiable"),
                    "fulliri_taxonomy_sha256": row.get("fulliri_taxonomy_sha256"),
                    "fulliri_nodes_sha256": row.get("fulliri_nodes_sha256"),
                    "fulliri_unsat_sha256": row.get("fulliri_unsat_sha256"),
                    "binary_sha256": row.get("binary_sha256"),
                    "binary_path": row.get("binary_path"),
                    "runtime_sha256": row.get("runtime_sha256"),
                    "source_ontology_sha256": row.get("source_ontology_sha256"),
                    "gold_kind": row.get("gold_kind"),
                    "gold_basename": row.get("gold_basename"),
                    "gold_sha256": row.get("gold_sha256"),
                    "signature_sha256": row.get("signature_sha256"),
                    "stderr_sha256": row.get("stderr_sha256"),
                    "reported_incomplete": row.get("reported_incomplete"),
                    "checkpointed": row.get("checkpointed"),
                    "output_format": row.get("output_format"),
                    "expressivity": row.get("expressivity"),
                    "fulliri_fingerprint_error": row.get(
                        "fulliri_fingerprint_error"
                    ),
                    "requested_route": row.get("requested_route"),
                    "command_json": json.dumps(row.get("command"), separators=(",", ":")),
                    "underlying_command_json": json.dumps(
                        row.get("underlying_command"), separators=(",", ":")
                    ),
                    "explicit_environment_json": json.dumps(
                        row.get("explicit_environment"), separators=(",", ":")
                    ),
                    "procedure_contract_json": json.dumps(
                        row.get("procedure_contract"), separators=(",", ":"), sort_keys=True
                    ),
                    "correctness_basis": row.get("correctness_basis"),
                    "pre_targeted_sound": row.get("pre_targeted_sound"),
                    "pre_targeted_complete": row.get("pre_targeted_complete"),
                    "pre_targeted_correctness_basis": row.get(
                        "pre_targeted_correctness_basis"
                    ),
                    "targeted_counterexample_count": row.get(
                        "targeted_counterexample_count"
                    ),
                    "targeted_counterexamples_json": json.dumps(
                        row.get("targeted_counterexamples"), separators=(",", ":")
                    ),
                    "targeted_adjudication_manifest_sha256": row.get(
                        "targeted_adjudication_manifest_sha256"
                    ),
                    "host": row.get("host"),
                    "cpu_model": row.get("cpu_model"),
                    "cpus": row.get("cpus"),
                    "slurm_job_id": row.get("slurm_job_id"),
                    "slurm_array_task_id": row.get("slurm_array_task_id"),
                    "order_index": row.get("order_index"),
                    "runner_sha256": row.get("runner_sha256"),
                    "runner_base_sha256": row.get("runner_base_sha256"),
                    "canonicalizer_sha256": row.get("canonicalizer_sha256"),
                    "watchdog_sha256": row.get("watchdog_sha256"),
                    "benchmark_driver_sha256": row.get("benchmark_driver_sha256"),
                    "fingerprint_driver_sha256": row.get("fingerprint_driver_sha256"),
                    "contract_sha256": row.get("contract_sha256"),
                    "build_receipt_sha256": row.get("build_receipt_sha256"),
                    "fulliri_fingerprint_json": row.get("fulliri_fingerprint_json"),
                    "fulliri_fingerprint_json_sha256": row.get(
                        "fulliri_fingerprint_json_sha256"
                    ),
                }
            )
    long_path.with_suffix(".tsv.tmp").replace(long_path)
    long_uncompressed_sha256 = sha256_file(long_path)
    long_gzip_path = args.output_dir / "full-panel-results.tsv.gz"
    with long_path.open("rb") as source, long_gzip_path.with_suffix(
        ".gz.tmp"
    ).open("wb") as destination:
        with gzip.GzipFile(
            filename="", mode="wb", fileobj=destination, compresslevel=9, mtime=0
        ) as compressed:
            shutil.copyfileobj(source, compressed, length=1 << 20)
    long_gzip_path.with_suffix(".gz.tmp").replace(long_gzip_path)
    long_path.unlink()

    summary_rows: list[dict] = []
    for procedure in contract:
        arm = procedure["arm"]
        arm_rows = [row for row in rows if row["arm"] == arm]
        summary_rows.append(
            summarize_rows(
                arm,
                procedure["family"],
                procedure["kind"],
                arm_rows,
                procedure,
            )
        )
    summary_fields = [key for key in summary_rows[0] if key != "procedure_contract"]
    summary_tsv = args.output_dir / "full-panel-summary.tsv"
    with summary_tsv.with_suffix(".tsv.tmp").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=summary_fields, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        for row in summary_rows:
            writer.writerow({key: row[key] for key in summary_fields})
    summary_tsv.with_suffix(".tsv.tmp").replace(summary_tsv)

    summary_json = args.output_dir / "full-panel-summary.json"
    atomic_text(
        summary_json,
        json.dumps(
            {
                "schema_version": 1,
                "ontology_count": len(ontologies),
                "procedure_count": len(contract),
                "measurement_count": len(rows),
                "distinct_slurm_task_job_ids": len(slurm_job_ids),
                "aggregation_slurm_job_id": os.environ.get("SLURM_JOB_ID"),
                "run_invariants": {field: rows[0][field] for field in invariant_files},
                "run_root": str(args.run_root),
                "procedures": summary_rows,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
    )

    effect_pairs = []
    previous_arm = OPTIMIZATION_STAGES[0][0]
    for optimized_arm, _revision in OPTIMIZATION_STAGES[1:]:
        effect_pairs.append(("chronological_stage", optimized_arm, previous_arm))
        previous_arm = optimized_arm
    effect_pairs.append(
        ("chronological_last_stage_to_frozen_main", "km_route_production_all", previous_arm)
    )
    for ablated_arm, _revision in OPTIMIZATION_ABLATIONS:
        effect_pairs.append(("clean_current_main_ablation", "km_route_production_all", ablated_arm))

    optimization_rows = []
    for comparison_kind, optimized_arm, reference_arm in effect_pairs:
        optimized = [by_ontology[ontology][optimized_arm] for ontology in ontologies]
        reference = [by_ontology[ontology][reference_arm] for ontology in ontologies]
        paired = [
            (new, old)
            for new, old in zip(optimized, reference)
            if new.get("status") == old.get("status") == "ok"
            and new.get("solved")
            and old.get("solved")
        ]
        wall_delta = [float(new["wall_s"]) - float(old["wall_s"]) for new, old in paired]
        peak_delta = [float(new["peak_mb"]) - float(old["peak_mb"]) for new, old in paired]
        optimization_rows.append(
            {
                "comparison_kind": comparison_kind,
                "optimized_arm": optimized_arm,
                "reference_arm": reference_arm,
                "optimized_sound_complete": sum(bool(row.get("solved")) for row in optimized),
                "reference_sound_complete": sum(bool(row.get("solved")) for row in reference),
                "sound_complete_delta": sum(bool(row.get("solved")) for row in optimized)
                - sum(bool(row.get("solved")) for row in reference),
                "paired_sound_complete": len(paired),
                "wall_mean_delta_s": metric(wall_delta, statistics.mean),
                "wall_median_delta_s": metric(wall_delta, statistics.median),
                "wall_faster": sum(delta < 0 for delta in wall_delta),
                "wall_equal": sum(delta == 0 for delta in wall_delta),
                "wall_slower": sum(delta > 0 for delta in wall_delta),
                "peak_mean_delta_mb": metric(peak_delta, statistics.mean),
                "peak_median_delta_mb": metric(peak_delta, statistics.median),
                "peak_lower": sum(delta < 0 for delta in peak_delta),
                "peak_equal": sum(delta == 0 for delta in peak_delta),
                "peak_higher": sum(delta > 0 for delta in peak_delta),
            }
        )
    optimization_path = args.output_dir / "optimization-effects.tsv"
    with optimization_path.with_suffix(".tsv.tmp").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(optimization_rows[0]),
            delimiter="\t",
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(optimization_rows)
    optimization_path.with_suffix(".tsv.tmp").replace(optimization_path)

    with args.existing_wide.open(newline="", encoding="utf-8") as handle:
        old_rows = list(csv.DictReader(handle, delimiter="\t"))
        old_fields = list(old_rows[0])
    if len(old_rows) != 592:
        raise SystemExit(f"existing wide table has {len(old_rows)} rows")

    documented_rows = []
    for old in old_rows:
        ontology = old["ontology"]
        documented_arm = documented_arm_for(old)
        if documented_arm:
            documented_rows.append(by_ontology[ontology][documented_arm])
        else:
            documented_rows.append(
                {
                    "ont": ontology,
                    "arm": "km_documented_selected",
                    "status": "no_claim",
                    "sound": "not_applicable",
                    "complete": "no",
                    "solved": False,
                }
            )

    headline_rows = [
        summarize_rows(
            "km_documented_selected",
            "virtual_selection",
            "km",
            documented_rows,
            {
                "selection": "the previously accepted per-ontology route; no route for an unclosed ontology",
            },
        )
    ]
    best_current_rows = []
    for ontology in ontologies:
        eligible = [
            row
            for row in by_ontology[ontology].values()
            if row.get("family") in {"km_route", "km_documented_solution_route"}
            and row.get("status") == "ok"
            and row.get("solved")
        ]
        if eligible:
            best_current_rows.append(min(eligible, key=lambda row: float(row["wall_s"])))
        else:
            best_current_rows.append(
                {
                    "ont": ontology,
                    "arm": "km_best_current_route",
                    "status": "no_claim",
                    "sound": "not_applicable",
                    "complete": "no",
                    "solved": False,
                }
            )
    headline_rows.append(
        summarize_rows(
            "km_best_current_route",
            "virtual_selection",
            "km",
            best_current_rows,
            {
                "selection": "fastest sound-and-complete current route per ontology; oracle upper bound",
            },
        )
    )
    for label, arm in STANDARD_ARMS.items():
        procedure = next(row for row in contract if row["arm"] == arm)
        headline_rows.append(
            summarize_rows(
                label,
                "headline",
                procedure["kind"],
                [by_ontology[ontology][arm] for ontology in ontologies],
                procedure,
            )
        )
    headline_fields = [key for key in headline_rows[0] if key != "procedure_contract"]
    headline_tsv = args.output_dir / "headline-summary.tsv"
    with headline_tsv.with_suffix(".tsv.tmp").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(
            handle, fieldnames=headline_fields, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        for row in headline_rows:
            writer.writerow({key: row[key] for key in headline_fields})
    headline_tsv.with_suffix(".tsv.tmp").replace(headline_tsv)
    headline_json = args.output_dir / "headline-summary.json"
    atomic_text(
        headline_json,
        json.dumps(
            {
                "schema_version": 1,
                "successful_metric_population": "status=ok rows only",
                "attempt_metric_population": "all rows with wall_s and peak_mb",
                "rows": headline_rows,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
    )

    extra_fields = ["full_panel_run_root"]
    for prefix in STANDARD_ARMS:
        extra_fields.extend(
            f"panel_{prefix}_{suffix}"
            for suffix in (
                "status",
                "wall_s",
                "peak_mb",
                "sound",
                "complete",
                "correctness_basis",
                "fulliri_taxonomy_sha256",
                "binary_sha256",
                "runtime_sha256",
            )
        )
    extra_fields.extend(
        [
            "panel_best_km_arm",
            "panel_best_km_wall_s",
            "panel_best_km_peak_mb",
            "panel_documented_route_arm",
            "panel_documented_route_status",
            "panel_documented_route_wall_s",
            "panel_documented_route_peak_mb",
            "panel_documented_route_sound",
            "panel_documented_route_complete",
            "panel_documented_route_correctness_basis",
            "panel_documented_route_fulliri_taxonomy_sha256",
            "panel_documented_route_binary_sha256",
            "panel_documented_route_runtime_sha256",
            "panel_documented_route_command_json",
            "panel_documented_route_explicit_environment_json",
            "panel_documented_route_slurm_job_id",
            "panel_documented_route_order_index",
            "panel_result_file",
            "panel_result_key",
            "panel_raw_result_file",
            "panel_all_procedures_json",
        ]
    )
    for old in old_rows:
        ontology = old["ontology"]
        indexed = by_ontology[ontology]
        old["full_panel_run_root"] = str(args.run_root)
        for prefix, arm in STANDARD_ARMS.items():
            row = indexed[arm]
            for suffix in (
                "status",
                "wall_s",
                "peak_mb",
                "sound",
                "complete",
                "correctness_basis",
                "fulliri_taxonomy_sha256",
                "binary_sha256",
                "runtime_sha256",
            ):
                old[f"panel_{prefix}_{suffix}"] = row.get(suffix, "")
        eligible = [
            row
            for row in indexed.values()
            if row.get("family") in {"km_route", "km_documented_solution_route"}
            and row.get("solved")
            and row.get("status") == "ok"
        ]
        best = min(eligible, key=lambda row: float(row["wall_s"])) if eligible else None
        old["panel_best_km_arm"] = best["arm"] if best else ""
        old["panel_best_km_wall_s"] = best["wall_s"] if best else ""
        old["panel_best_km_peak_mb"] = best["peak_mb"] if best else ""

        documented_arm = documented_arm_for(old)
        documented = indexed.get(documented_arm) if documented_arm else None
        old["panel_documented_route_arm"] = documented_arm
        for suffix in (
            "status",
            "wall_s",
            "peak_mb",
            "sound",
            "complete",
            "correctness_basis",
            "fulliri_taxonomy_sha256",
            "binary_sha256",
            "runtime_sha256",
            "slurm_job_id",
            "order_index",
        ):
            old[f"panel_documented_route_{suffix}"] = documented.get(suffix, "") if documented else ""
        old["panel_documented_route_command_json"] = (
            json.dumps(documented.get("command"), separators=(",", ":")) if documented else ""
        )
        old["panel_documented_route_explicit_environment_json"] = (
            json.dumps(documented.get("explicit_environment"), separators=(",", ":"))
            if documented
            else ""
        )
        old["panel_result_file"] = "full-panel-results.tsv.gz"
        old["panel_result_key"] = ontology
        old["panel_raw_result_file"] = str(
            args.run_root / "results" / f"{ontology}.jsonl"
        )
        old["panel_all_procedures_json"] = json.dumps(
            [
                {
                    key: indexed[arm].get(key)
                    for key in (
                        "arm",
                        "family",
                        "status",
                        "rc",
                        "wall_s",
                        "peak_mb",
                        "sound",
                        "complete",
                        "solved",
                        "correctness_basis",
                        "verdict",
                        "fulliri_verdict",
                        "targeted_counterexample_count",
                        "reported_incomplete",
                        "fulliri_taxonomy_sha256",
                        "binary_sha256",
                        "runtime_sha256",
                        "slurm_job_id",
                        "order_index",
                    )
                }
                for arm in arms
            ],
            separators=(",", ":"),
        )

    wide_path = args.output_dir / "ontology-route-performance.tsv"
    with wide_path.with_suffix(".tsv.tmp").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=old_fields + extra_fields,
            delimiter="\t",
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(old_rows)
    wide_path.with_suffix(".tsv.tmp").replace(wide_path)

    adjudication_path = args.output_dir / "ore-4669-targeted-soundness.tsv"
    with adjudication_path.with_suffix(".tsv.tmp").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(adjudication_rows[0]),
            delimiter="\t",
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(adjudication_rows)
    adjudication_path.with_suffix(".tsv.tmp").replace(adjudication_path)

    raw_manifest_path = args.output_dir / "full-panel-raw-results.sha256"
    atomic_text(
        raw_manifest_path,
        "".join(
            f"{sha256_file(args.run_root / 'results' / f'{ontology}.jsonl')}  "
            f"results/{ontology}.jsonl\n"
            for ontology in ontologies
        ),
    )
    raw_gzip_path = args.output_dir / "full-panel-raw-results.jsonl.gz"
    with raw_gzip_path.with_suffix(".gz.tmp").open("wb") as destination:
        with gzip.GzipFile(
            filename="", mode="wb", fileobj=destination, compresslevel=9, mtime=0
        ) as compressed:
            for ontology in ontologies:
                with (
                    args.run_root / "results" / f"{ontology}.jsonl"
                ).open("rb") as source:
                    shutil.copyfileobj(source, compressed, length=1 << 20)
    raw_gzip_path.with_suffix(".gz.tmp").replace(raw_gzip_path)

    receipt_path = args.output_dir / "full-panel-receipt.json"
    atomic_text(
        receipt_path,
        json.dumps(
            {
                "schema_version": 1,
                "run_root": str(args.run_root),
                "array_job_id": args.run_root.name,
                "existing_wide_input": str(args.existing_wide),
                "existing_wide_input_sha256": sha256_file(args.existing_wide),
                "ontology_list": str(args.ontology_list),
                "ontology_list_sha256": sha256_file(args.ontology_list),
                "ontology_count": len(ontologies),
                "procedure_count": len(contract),
                "measurement_count": len(rows),
                "distinct_slurm_task_job_ids": len(slurm_job_ids),
                "aggregation_slurm_job_id": os.environ.get("SLURM_JOB_ID"),
                "run_invariants": {field: rows[0][field] for field in invariant_files},
                "array_driver_manifest": str(args.array_driver_manifest),
                "array_driver_manifest_sha256": sha256_file(
                    args.array_driver_manifest
                ),
                "supplemental_driver_manifest": str(
                    args.supplemental_driver_manifest
                ),
                "supplemental_driver_manifest_sha256": sha256_file(
                    args.supplemental_driver_manifest
                ),
                "supplemental_driver_entries_verified": len(supplemental_entries),
                "primary_runner_sha256": primary_runner_sha,
                "supplemental_runner_sha256": supplemental_runner_sha,
                "fulliri_only_ontologies": sorted(FULLIRI_ONLY_ONTOLOGIES),
                "build_receipt": str(args.build_receipt),
                "build_receipt_sha256": sha256_file(args.build_receipt),
                "binary_manifest": str(args.binary_manifest),
                "binary_manifest_sha256": sha256_file(args.binary_manifest),
                "binary_manifest_entries_verified": len(binary_entries),
                "km_variant_receipts_verified": len(variant_receipt_hashes),
                "km_variant_receipts_named_digest_sha256": named_digests_sha256(
                    variant_receipt_hashes
                ),
                "ablation_patches_manifest": str(args.ablation_patches_manifest),
                "ablation_patches_manifest_sha256": sha256_file(
                    args.ablation_patches_manifest
                ),
                "ablation_patch_entries_verified": len(patch_entries),
                "array_driver_entries_verified": len(driver_entries),
                "adjudication_4669_manifest": str(args.adjudication_4669_manifest),
                "adjudication_4669_manifest_sha256": sha256_file(
                    args.adjudication_4669_manifest
                ),
                "adjudication_4669_source_ontology_sha256": (
                    ADJUDICATION_4669_SOURCE_SHA256
                ),
                "adjudication_4669_array_job_ids": [
                    "49075466",
                    "49075584",
                    "49075857",
                    "49076590",
                ],
                "adjudication_4669_output_sha256": sha256_file(adjudication_path),
                "raw_results_manifest_sha256": sha256_file(raw_manifest_path),
                "raw_results_gzip_sha256": sha256_file(raw_gzip_path),
                "full_panel_contract_tsv_sha256": sha256_file(contract_path),
                "procedure_runtime_identities_tsv_sha256": sha256_file(
                    identity_path
                ),
                "full_panel_results_uncompressed_sha256": long_uncompressed_sha256,
                "full_panel_results_gzip_sha256": sha256_file(long_gzip_path),
                "full_panel_summary_tsv_sha256": sha256_file(summary_tsv),
                "full_panel_summary_json_sha256": sha256_file(summary_json),
                "headline_summary_tsv_sha256": sha256_file(headline_tsv),
                "headline_summary_json_sha256": sha256_file(headline_json),
                "optimization_effects_tsv_sha256": sha256_file(optimization_path),
                "ontology_route_performance_sha256": sha256_file(wide_path),
                "aggregator_sha256": sha256_file(Path(__file__)),
                "contract_sha256": sha256_file(Path(__file__).with_name("full_panel_contract.py")),
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
    )
    generated_manifest = args.output_dir / "full-panel-generated-files.sha256"
    generated_files = (
        contract_path,
        identity_path,
        long_gzip_path,
        summary_tsv,
        summary_json,
        headline_tsv,
        headline_json,
        optimization_path,
        wide_path,
        adjudication_path,
        raw_manifest_path,
        raw_gzip_path,
        receipt_path,
    )
    atomic_text(
        generated_manifest,
        "".join(f"{sha256_file(path)}  {path.name}\n" for path in generated_files),
    )
    print(
        json.dumps(
            {
                "ontology_count": len(ontologies),
                "procedure_count": len(contract),
                "measurement_count": len(rows),
                "receipt": str(receipt_path),
                "generated_manifest": str(generated_manifest),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
