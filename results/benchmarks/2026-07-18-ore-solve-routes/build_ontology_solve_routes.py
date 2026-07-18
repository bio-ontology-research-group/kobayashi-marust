#!/usr/bin/env python3
"""Build one actionable KM route row for every ORE 2015 ontology."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path


TIMEOUT_S = 240
MEMORY_LIMIT_MB = 20 * 1024
CPUS = 16
BASE_REGISTRY_SHA256 = (
    "90eff8539618605b1ccdef5b367518ea8cbc5f6a19d14deabe909abef86e64ea"
)
BASE_REGISTRY_SOURCE = (
    "ibex:/ibex/scratch/hohndor/km/routing_20260715/candidates/feb0cc6/"
    "source.tar.gz!results/benchmarks/2026-07-16-routing-complete592/"
    "ontology-routes.tsv"
)

FIELDS = [
    "ontology",
    "state",
    "route",
    "route_kind",
    "within_limits",
    "verdict",
    "wall_s",
    "peak_mb",
    "timeout_s",
    "memory_limit_mb",
    "cpus",
    "binary_sha256",
    "binary_locator",
    "source_revision",
    "route_environment",
    "invocation",
    "gold_kind",
    "gold_sha256",
    "signature_sha256",
    "other_verified_exact_routes",
    "evidence",
    "notes",
]

OLD_COMMIT_BINARY = (
    "ibex:/ibex/scratch/hohndor/km/routing_20260715/"
    "retained-route-rerun-20260718/target/release/km"
)
CURRENT_CANDIDATE_BINARY = (
    "ibex:/ibex/scratch/hohndor/km/routing_20260715/candidates/feb0cc6/km"
)
KPSET_BINARY = (
    "ibex:/ibex/scratch/hohndor/km/3215_closure_20260713/"
    "km-3215-bullseye"
)
ATLEAST_BINARY = (
    "ibex:/ibex/scratch/hohndor/km/14817_closure_20260714/"
    "km-14817-atleast"
)

PRODUCTION_BINARY_METADATA = {
    "86eb38310683ab964d88ed87a86b61811fb6e2debc843f2c91c784c4bf535230": (
        "ibex:/ibex/scratch/hohndor/km/routing_20260715/"
        "candidate-a068059/km",
        "candidate-a068059",
    ),
    "60f147d5af3d300895fdad3eb41fff70443dff060bdac8fe7e3b2a434302acd9": (
        "ibex:/ibex/scratch/hohndor/km/routing_20260715/"
        "candidates/a0d0148816c5/km",
        "candidate-a0d0148816c5",
    ),
    "8771789c1afe5e80471caa9f7ed263eab2ab09af48673d1cb3f6b7ec0aa6284d": (
        "ibex:/ibex/scratch/hohndor/km/routing_20260715/"
        "candidates/a639ab5/km",
        "candidate-a639ab5",
    ),
}

COMMON_MANUAL = (
    "KM_ROUTE=manual KM_THREADS=16 KM_PAR_MEM_GB=18 KM_HT_MEM_GB=18 "
    "KM_KEEP_CHAIN_AXIOMS=1"
)
COMMON_PRODUCTION = (
    "KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 "
    "KM_BRIDGE_PROBE_BUDGET_S=30 KM_BRIDGE_RETRY_ROUNDS=0 "
    "KM_HT_SATURATION_BUDGET_S=180 KM_HT_MEM_GB=18 "
    "KM_PAR_MEM_GB=18 KM_THREADS=16"
)

# Each entry names the exact environment used by the 2026-07-18 retained-route
# rerun. These labels are empirical per-ontology routes, not general fallbacks.
RETAINED_EXACT = {
    "ore_ont_10702.owl": {
        "file": "nomlink_default__ore_ont_10702.owl.jsonl",
        "route": "nomlink_default",
        "env": COMMON_MANUAL,
        "binary_locator": OLD_COMMIT_BINARY,
        "source_revision": "git:0d20dd1",
    },
    "ore_ont_10908.owl": {
        "file": "shoq_race__ore_ont_10908.owl.jsonl",
        "route": "shoq_race",
        "env": (
            f"{COMMON_MANUAL} KM_HT_MODE=race KM_NO_HT_QO_ROUTER=1 "
            "KM_NO_HT_CARD=1 KM_NO_ELC_PORTFOLIO=1 "
            "KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0"
        ),
        "binary_locator": OLD_COMMIT_BINARY,
        "source_revision": "git:0d20dd1",
    },
    "ore_ont_11745.owl": {
        "file": "production_all__ore_ont_11745.owl.jsonl",
        "route": "production_all",
        "env": (
            "KM_ROUTE=production_all KM_THREADS=16 KM_PAR_MEM_GB=18 "
            "KM_TRIGGER_ABSORB=1 KM_BRIDGE_PROBE_BUDGET_S=30 "
            "KM_BRIDGE_RETRY_ROUNDS=0 KM_HT_SATURATION_BUDGET_S=180"
        ),
        "binary_locator": CURRENT_CANDIDATE_BINARY,
        "source_revision": "candidate-feb0cc6",
    },
    "ore_ont_15672.owl": {
        "file": "shoq_race__ore_ont_15672.owl.jsonl",
        "route": "shoq_race",
        "env": (
            f"{COMMON_MANUAL} KM_HT_MODE=race KM_NO_HT_QO_ROUTER=1 "
            "KM_NO_HT_CARD=1 KM_NO_ELC_PORTFOLIO=1 "
            "KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0"
        ),
        "binary_locator": OLD_COMMIT_BINARY,
        "source_revision": "git:0d20dd1",
    },
    "ore_ont_6934.owl": {
        "file": "htforce_race__ore_ont_6934.owl.jsonl",
        "route": "htforce_race",
        "env": (
            "KM_THREADS=16 KM_PAR_MEM_GB=18 KM_HT_MEM_GB=18 "
            "KM_KEEP_CHAIN_AXIOMS=1 KM_ABSORB=1 KM_ABSORB_PORTFOLIO=1 "
            "KM_HT_FORCE=1 KM_HT_MODE=race"
        ),
        "binary_locator": OLD_COMMIT_BINARY,
        "source_revision": "git:0d20dd1",
    },
    "ore_ont_7499.owl": {
        "file": "card_race__ore_ont_7499.owl.jsonl",
        "route": "card_race",
        "env": (
            f"{COMMON_MANUAL} KM_HT_MODE=race KM_NO_HT_QO_ROUTER=1 "
            "KM_NO_HT_SHOQ=1 KM_NO_ELC_PORTFOLIO=1 "
            "KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0"
        ),
        "binary_locator": OLD_COMMIT_BINARY,
        "source_revision": "git:0d20dd1",
    },
    "ore_ont_9540.owl": {
        "file": "card_race__ore_ont_9540.owl.jsonl",
        "route": "card_race",
        "env": (
            f"{COMMON_MANUAL} KM_HT_MODE=race KM_NO_HT_QO_ROUTER=1 "
            "KM_NO_HT_SHOQ=1 KM_NO_ELC_PORTFOLIO=1 "
            "KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0"
        ),
        "binary_locator": OLD_COMMIT_BINARY,
        "source_revision": "git:0d20dd1",
    },
    "ore_ont_9635.owl": {
        "file": "legacy_tab_race__ore_ont_9635.owl.jsonl",
        "route": "legacy_tab_race",
        "env": (
            f"{COMMON_MANUAL} KM_TAB_RACE=1 KM_TAB_FEAT=1 "
            "KM_TAB_RACE_DELAY=0 KM_NO_HT_RACE=1 KM_NO_ELC_PORTFOLIO=1 "
            "KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0"
        ),
        "binary_locator": OLD_COMMIT_BINARY,
        "source_revision": "git:0d20dd1",
    },
    "ore_ont_3215.owl": {
        "file": "kpset_barrier_retry__ore_ont_3215.owl.jsonl",
        "route": "kpset_barrier",
        "env": COMMON_PRODUCTION,
        "binary_locator": KPSET_BINARY,
        "source_revision": "2026-07-13-kpset-closure",
    },
}

SPECIAL_IRI_FIX_BINARY_SHA256 = (
    "6dd3a33c62018b177c01967af5784303c7b18f2657f730ec60643d1fb4e227df"
)

SPECIAL_IRI_FIXED = {
    "ore_ont_13503.owl": {
        "reference": "konclude_fulliri_audit_13503",
        "reference_fingerprint": "fulliri-source.json",
        "gold_kind": "fresh Konclude full-IRI; HermiT class query",
        "note": (
            "The legal daml+oil#Nothing source class remains named and is "
            "reported UNSAT; the full-IRI taxonomy matches Konclude."
        ),
    },
    "ore_ont_3524.owl": {
        "reference": "konclude_w16_3524",
        "reference_fingerprint": "fulliri.json",
        "gold_kind": "fresh Konclude full-IRI; ELK corroboration",
        "told_target": True,
        "note": (
            "All 123310 strict told subsumptions to the legal nested #Thing "
            "class are preserved; the full-IRI taxonomy matches Konclude."
        ),
    },
    "ore_ont_15703.owl": {
        "reference": "konclude_w16_15703",
        "reference_fingerprint": "fulliri.json",
        "gold_kind": "fresh Konclude full-IRI; ELK corroboration",
        "told_target": True,
        "note": (
            "All 123310 told subsumptions to the legal nested #Thing class "
            "are preserved; the full-IRI taxonomy matches Konclude."
        ),
    },
    "ore_ont_7581.owl": {
        "reference": "konclude_fulliri_audit_7581",
        "reference_fingerprint": "fulliri-source.json",
        "gold_kind": "fresh Konclude full-IRI",
        "note": (
            "The source-IRI fix preserves the previously exact 7581 taxonomy; "
            "the fresh full-IRI fingerprint still matches Konclude."
        ),
    },
}

COMPLETED_INCORRECT = {
    "ore_ont_4669.owl": {
        "label": "km_production_4669",
        "verdict": "unsound",
        "route": "production_default",
        "env": COMMON_PRODUCTION,
        "binary_locator": KPSET_BINARY,
        "source_revision": "2026-07-13-kpset-closure",
    },
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def ontology_key(name: str) -> int:
    match = re.fullmatch(r"ore_ont_(\d+)\.owl", name)
    if not match:
        raise ValueError(f"unexpected ontology name: {name}")
    return int(match.group(1))


def read_single_jsonl(path: Path) -> dict:
    rows = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    if len(rows) != 1:
        raise ValueError(f"expected one JSON row in {path}, found {len(rows)}")
    return rows[0]


def common_row(ontology: str) -> dict[str, str]:
    return {
        "ontology": ontology,
        "state": "",
        "route": "",
        "route_kind": "",
        "within_limits": "",
        "verdict": "",
        "wall_s": "",
        "peak_mb": "",
        "timeout_s": str(TIMEOUT_S),
        "memory_limit_mb": str(MEMORY_LIMIT_MB),
        "cpus": str(CPUS),
        "binary_sha256": "",
        "binary_locator": "",
        "source_revision": "",
        "route_environment": "",
        "invocation": "",
        "gold_kind": "",
        "gold_sha256": "",
        "signature_sha256": "",
        "other_verified_exact_routes": "",
        "evidence": "",
        "notes": "",
    }


def base_production_row(source: dict[str, str]) -> dict[str, str]:
    row = common_row(source["ontology"])
    locator, revision = PRODUCTION_BINARY_METADATA[source["binary_sha256"]]
    row.update(
        {
            "state": "exact_gold",
            "route": "production_all",
            "route_kind": "named_production",
            "within_limits": "yes",
            "verdict": "match",
            "wall_s": source["wall_s"],
            "peak_mb": source["peak_mb"],
            "binary_sha256": source["binary_sha256"],
            "binary_locator": locator,
            "source_revision": revision,
            "route_environment": "KM_ROUTE=production_all",
            "invocation": source["invocation"],
            "gold_kind": source["gold_kind"],
            "gold_sha256": source["gold_sha256"],
            "signature_sha256": source["signature_sha256"],
            "evidence": f"{BASE_REGISTRY_SOURCE} -> {source['evidence']}",
            "notes": "Gold-exact production sweep.",
        }
    )
    return row


def retained_exact_row(
    ontology: str, spec: dict[str, str], evidence_dir: Path
) -> dict[str, str]:
    path = evidence_dir / spec["file"]
    source = read_single_jsonl(path)
    if source.get("ont") != ontology:
        raise ValueError(f"ontology mismatch in {path}")
    if source.get("status") != "ok" or source.get("verdict") != "match":
        raise ValueError(f"retained route is not exact in {path}")
    wall = float(source["wall_s"])
    peak = float(source["peak_mb"])
    if wall > TIMEOUT_S or peak > MEMORY_LIMIT_MB:
        raise ValueError(f"retained route exceeds limits in {path}")
    if int(source["cpus"]) != CPUS:
        raise ValueError(f"unexpected CPU count in {path}")

    row = common_row(ontology)
    row.update(
        {
            "state": "exact_gold",
            "route": spec["route"],
            "route_kind": (
                "named_production"
                if spec["route"] == "production_all"
                else "retained_per_ontology"
            ),
            "within_limits": "yes",
            "verdict": "match",
            "wall_s": str(source["wall_s"]),
            "peak_mb": str(source["peak_mb"]),
            "binary_sha256": source["binary_sha256"],
            "binary_locator": spec["binary_locator"],
            "source_revision": spec["source_revision"],
            "route_environment": spec["env"],
            "invocation": (
                f"env {spec['env']} $KM_BIN classify $ORE_CORPUS/{ontology}"
            ),
            "gold_kind": source["gold_kind"],
            "gold_sha256": source["gold_sha256"],
            "signature_sha256": source["signature_sha256"],
            "evidence": str(path),
            "notes": (
                "Exact retained-route rerun; missing=0, extra=0, "
                f"missing_unsat=0, extra_unsat=0; Slurm job "
                f"{source['slurm_job_id']}."
            ),
        }
    )
    return row


def read_json(path: Path) -> dict:
    return json.loads(path.read_text())


def completed_incorrect_row(
    ontology: str, spec: dict[str, str], direct_dir: Path
) -> dict[str, str]:
    result_dir = direct_dir / "results" / spec["label"]
    validation_path = result_dir / "validation.json"
    source = read_json(validation_path)
    run = source["run"]
    if run.get("status") != "ok" or run.get("return_code") != 0:
        raise ValueError(f"expected successful KM process in {validation_path}")

    evidence = [validation_path]
    gold_kind = "HermiT targeted satisfiability"
    gold_sha256 = ""
    signature_sha256 = ""
    if spec["verdict"] == "incomplete":
        special_named_bottom = spec.get("special_named_bottom") == "yes"
        fingerprint_name = "fulliri-source.json" if special_named_bottom else "fulliri.json"
        km_fingerprint_path = result_dir / fingerprint_name
        reference_path = (
            direct_dir / "results" / spec["reference"] / fingerprint_name
        )
        km_fingerprint = read_json(km_fingerprint_path)
        reference = read_json(reference_path)
        if km_fingerprint["taxonomy_sha256"] == reference["taxonomy_sha256"]:
            raise ValueError(f"unexpected equal full-IRI fingerprints for {ontology}")
        evidence.extend((km_fingerprint_path, reference_path))
        gold_sha256 = reference["taxonomy_sha256"]
        signature_sha256 = km_fingerprint["taxonomy_sha256"]
        if special_named_bottom:
            query_path = (
                direct_dir / "13503-satisfiability" / "0.stdout.validation.json"
            )
            query = read_json(query_path)
            if (
                km_fingerprint["unsatisfiable"] != 0
                or reference["unsatisfiable"] != 1
                or query["status"] != "ok"
                or query["satisfiable"] is not False
            ):
                raise ValueError("13503 named-bottom counterexample is incomplete")
            evidence.append(query_path)
            gold_kind = "fresh Konclude full-IRI; HermiT class query"
            notes = (
                "KM terminates but omits the unsatisfiable legal source class "
                "daml+oil#Nothing after parsing it as owl:Nothing."
            )
        else:
            ontology_id = ontology.removeprefix("ore_ont_").removesuffix(".owl")
            elk_path = direct_dir / "results" / f"elk_{ontology_id}" / "fulliri.json"
            told_path = result_dir / "told-target-validation.json"
            elk = read_json(elk_path)
            told = read_json(told_path)
            if told.get("verdict") != "incomplete":
                raise ValueError(f"missing told-axiom counterexample in {told_path}")
            if elk["taxonomy_sha256"] != reference["taxonomy_sha256"]:
                raise ValueError(f"Konclude/ELK full-IRI disagreement for {ontology}")
            evidence.extend((elk_path, told_path))
            gold_kind = "fresh Konclude full-IRI; ELK corroboration"
            notes = (
                "KM terminates but omits 123310 strict told subsumptions. "
                "A legal source IRI ending in #Thing is parsed as OWL top."
            )
    else:
        signature_sha256 = source["canonicalization"]["signature_sha256"]
        ht_query_dir = direct_dir / "4669-satisfiability"
        sample_dir = direct_dir / "4669-production-unsat-sample"
        single_dir = direct_dir / "4669-positive-control"
        ht_queries = [read_json(path) for path in ht_query_dir.glob("*.json")]
        sampled = [read_json(path) for path in sample_dir.glob("*.json")]
        sampled += [read_json(path) for path in single_dir.glob("*.json")]
        expected_ht_classes = {
            line
            for line in (
                direct_dir.parent / "ore_ont_4669-ht-only-unsat.txt"
            ).read_text().splitlines()
            if line
        }
        if len(ht_queries) != 56 or not all(
            row["status"] == "ok" and row["satisfiable"] is True
            for row in ht_queries
        ):
            raise ValueError("4669 HT counterexample set is incomplete")
        if {row["class"] for row in ht_queries} != expected_ht_classes:
            raise ValueError("4669 HT query classes do not match the route diff")
        proven_satisfiable = {
            row["class"]
            for row in sampled
            if row["status"] == "ok" and row["satisfiable"] is True
        }
        if len(proven_satisfiable) != 8:
            raise ValueError("expected eight production-UNSAT counterexamples")
        evidence.extend((ht_query_dir, sample_dir, single_dir))
        notes = (
            "KM terminates but is unsound: HermiT proves eight sampled "
            "production-UNSAT classes satisfiable. HermiT also proves all 56 "
            "additional HT-UNSAT classes satisfiable."
        )

    row = common_row(ontology)
    row.update(
        {
            "state": "completed_incorrect",
            "route": spec["route"],
            "route_kind": "retained_production_binary",
            "within_limits": "yes",
            "verdict": spec["verdict"],
            "wall_s": str(run["wall_s"]),
            "peak_mb": str(run["peak_mb"]),
            "binary_sha256": run["binary_sha256"],
            "binary_locator": spec["binary_locator"],
            "source_revision": spec["source_revision"],
            "route_environment": spec["env"],
            "invocation": (
                f"env {spec['env']} $KM_BIN classify $ORE_CORPUS/{ontology}"
            ),
            "gold_kind": gold_kind,
            "gold_sha256": gold_sha256,
            "signature_sha256": signature_sha256,
            "evidence": "; ".join(str(path) for path in evidence),
            "notes": notes,
        }
    )
    return row


def direct_special_iri_exact_row(
    ontology: str, spec: dict, direct_dir: Path
) -> dict[str, str]:
    ontology_id = ontology.removeprefix("ore_ont_").removesuffix(".owl")
    km_dir = direct_dir / "results" / f"km_special_iri_main_{ontology_id}"
    reference_dir = direct_dir / "results" / spec["reference"]
    run_path = km_dir / "run.json"
    verdict_path = km_dir / "direct-verdict.json"
    km_fingerprint_path = km_dir / "fulliri-source.json"
    reference_path = reference_dir / spec["reference_fingerprint"]
    run = read_json(run_path)
    verdict = read_json(verdict_path)
    km_fingerprint = read_json(km_fingerprint_path)
    reference = read_json(reference_path)
    if (
        run["status"] != "ok"
        or run["return_code"] != 0
        or run["binary_sha256"] != SPECIAL_IRI_FIX_BINARY_SHA256
        or int(run["cpus"]) != CPUS
        or float(run["wall_s"]) > TIMEOUT_S
        or float(run["peak_mb"]) > MEMORY_LIMIT_MB
        or verdict["verdict"] != "match"
        or km_fingerprint["taxonomy_sha256"] != reference["taxonomy_sha256"]
        or km_fingerprint["subsumptions"] != reference["subsumptions"]
        or km_fingerprint["unsatisfiable"] != reference["unsatisfiable"]
    ):
        raise ValueError(f"{ontology} failed its fixed full-IRI revalidation")

    evidence = [run_path, verdict_path, km_fingerprint_path, reference_path]
    if spec.get("told_target"):
        told_path = km_dir / "told-target-validation.json"
        told = read_json(told_path)
        if (
            told.get("verdict") != "preserved"
            or told.get("missing_told_subsumptions") != 0
            or told.get(
                "told_compared_distinct_lefts", told.get("told_distinct_lefts")
            )
            != 123310
        ):
            raise ValueError(f"{ontology} still omits a strict told subsumption")
        evidence.append(told_path)

    if ontology == "ore_ont_13503.owl":
        query_path = direct_dir / "13503-satisfiability" / "0.stdout.validation.json"
        query = read_json(query_path)
        if query["status"] != "ok" or query["satisfiable"] is not False:
            raise ValueError("13503 HermiT named-bottom validation is incomplete")
        evidence.append(query_path)

    row = common_row(ontology)
    row.update(
        {
            "state": "exact_gold",
            "route": "production_all",
            "route_kind": (
                "direct_full_iri_recheck"
                if ontology == "ore_ont_7581.owl"
                else "direct_special_iri_fix"
            ),
            "within_limits": "yes",
            "verdict": "match",
            "wall_s": str(run["wall_s"]),
            "peak_mb": str(run["peak_mb"]),
            "binary_sha256": run["binary_sha256"],
            "binary_locator": f"ibex:{run['binary']}",
            "source_revision": "candidate:ab1d457+special-iri-main-20260718",
            "route_environment": "KM_ROUTE=production_all",
            "invocation": (
                "env KM_ROUTE=production_all $KM_BIN classify "
                f"$ORE_CORPUS/{ontology}"
            ),
            "gold_kind": spec["gold_kind"],
            "gold_sha256": reference["taxonomy_sha256"],
            "signature_sha256": km_fingerprint["taxonomy_sha256"],
            "evidence": "; ".join(str(path) for path in evidence),
            "notes": spec["note"],
        }
    )
    return row


def unresolved_rows(direct_dir: Path) -> dict[str, dict[str, str]]:
    rows: dict[str, dict[str, str]] = {}
    for ontology in ("ore_ont_2669.owl", "ore_ont_15516.owl"):
        ontology_id = ontology.removeprefix("ore_ont_").removesuffix(".owl")
        km_path = direct_dir / "results" / f"km_ht_rules_{ontology_id}" / "validation.json"
        hermit_path = (
            direct_dir / "results" / f"hermit_core_{ontology_id}" / "validation.json"
        )
        km = read_json(km_path)
        hermit = read_json(hermit_path)
        km_signature = km["canonicalization"]["signature_sha256"]
        if (
            km["run"]["status"] != "ok"
            or km["canonicalization"]["consistent"] is not False
            or hermit["canonicalization"]["signature_sha256"] != km_signature
        ):
            raise ValueError(f"failed inconsistent-core validation for {ontology}")
        row = common_row(ontology)
        row.update(
            {
                "state": "adjudicated_correct_stale_gold",
                "route": "ht_rules",
                "route_kind": "adjudicated_special",
                "within_limits": "yes",
                "verdict": "correct_inconsistent_stale_gold",
                "wall_s": str(km["run"]["wall_s"]),
                "peak_mb": str(km["run"]["peak_mb"]),
                "binary_sha256": km["run"]["binary_sha256"],
                "binary_locator": OLD_COMMIT_BINARY,
                "source_revision": "git:0d20dd1",
                "route_environment": "KM_HT_RULES=1",
                "invocation": (
                    f"env KM_HT_RULES=1 $KM_BIN classify $ORE_CORPUS/{ontology}"
                ),
                "gold_kind": "HermiT cleaned inconsistent core",
                "signature_sha256": km_signature,
                "evidence": f"{km_path}; {hermit_path}; docs/CONTESTED-GOLD.md",
                "notes": (
                    "KM returns the adjudicated inconsistent verdict. The stored "
                    "Konclude signature is a parse-failure artifact, so this row "
                    "is intentionally not counted as exact_gold."
                ),
            }
        )
        rows[ontology] = row

    row = common_row("ore_ont_10621.owl")
    km_path = direct_dir / "results" / "km_production_c229_10621" / "validation.json"
    konclude_path = direct_dir / "results" / "konclude_w16_10621" / "validation.json"
    compare_path = direct_dir / "ore_ont_10621-gold-compare.json"
    km = read_json(km_path)
    konclude = read_json(konclude_path)
    comparison = read_json(compare_path)
    if (
        km["run"]["status"] != "timeout"
        or konclude["run"]["status"] != "ok"
        or comparison["line_equal"] is not True
    ):
        raise ValueError("10621 direct validation does not match the registry state")
    row.update(
        {
            "state": "no_complete_within_limit_valid_gold",
            "route_kind": "none_verified",
            "within_limits": "no",
            "verdict": "timeout",
            "wall_s": str(km["run"]["wall_s"]),
            "peak_mb": str(km["run"]["peak_mb"]),
            "gold_kind": "fresh Konclude matches stored gold",
            "gold_sha256": comparison["stored_signature_sha256"],
            "evidence": f"{km_path}; {konclude_path}; {compare_path}",
            "notes": (
                "Fresh Konclude includes the functional-datatype UNSAT result "
                "and is line-identical to current stored gold. No full KM "
                "classification completes within 240 s and 20 GiB."
            ),
        }
    )
    rows[row["ontology"]] = row

    for ontology, note in {
        "ore_ont_10860.owl": (
            "No authoritative full gold and no retained complete KM route. The "
            "raw ontology contains unsupported DL-safe rules."
        ),
        "ore_ont_1194.owl": (
            "No authoritative full gold and no retained complete KM route; the "
            "tested completion routes reached the memory limit."
        ),
    }.items():
        row = common_row(ontology)
        row.update(
            {
                "state": "unresolved_no_authoritative_gold",
                "route_kind": "none_verified",
                "within_limits": "no",
                "verdict": "unresolved",
                "gold_kind": "none",
                "evidence": (
                    f"{direct_dir / 'validation-summary.tsv'}; "
                    f"{direct_dir / 'results'}"
                ),
                "notes": note,
            }
        )
        rows[ontology] = row
    return rows


def build(args: argparse.Namespace) -> list[dict[str, str]]:
    base_path = Path(args.base_registry)
    if sha256(base_path) != BASE_REGISTRY_SHA256:
        raise ValueError("base registry SHA-256 does not match the frozen input")

    with base_path.open(newline="") as handle:
        base_rows = list(csv.DictReader(handle, delimiter="\t"))
    grouped: dict[str, list[dict[str, str]]] = defaultdict(list)
    for source in base_rows:
        grouped[source["ontology"]].append(source)
    if len(grouped) != 592:
        raise ValueError(f"expected 592 ontologies, found {len(grouped)}")

    exact_routes: dict[str, dict[str, float]] = defaultdict(dict)
    selected: dict[str, dict[str, str]] = {}
    for ontology, sources in grouped.items():
        for source in sources:
            if source["state"] == "exact_gold" and source["verdict"] == "match":
                wall = float(source["wall_s"])
                prior = exact_routes[ontology].get(source["route"])
                if prior is None or wall < prior:
                    exact_routes[ontology][source["route"]] = wall
        production = [
            source
            for source in sources
            if source["route"] == "production_all"
            and source["state"] == "exact_gold"
            and source["verdict"] == "match"
        ]
        if len(production) == 1:
            selected[ontology] = base_production_row(production[0])

    retained_dir = Path(args.retained_evidence)
    for ontology, spec in RETAINED_EXACT.items():
        row = retained_exact_row(ontology, spec, retained_dir)
        selected[ontology] = row
        wall = float(row["wall_s"])
        prior = exact_routes[ontology].get(row["route"])
        if prior is None or wall < prior:
            exact_routes[ontology][row["route"]] = wall

    direct_dir = Path(args.direct_validation)
    audit_rows = [
        json.loads(line)
        for path in (direct_dir / "special-iri-audit").glob("*.jsonl")
        for line in path.read_text().splitlines()
        if line
    ]
    if len(audit_rows) != 912 or len({row["ontology"] for row in audit_rows}) != 912:
        raise ValueError("special-IRI source audit is incomplete")
    collision_registry_rows = {
        row["ontology"]
        for row in audit_rows
        if row["collision_count"] and row["ontology"] in grouped
    }
    if collision_registry_rows != {
        "ore_ont_3524.owl",
        "ore_ont_4669.owl",
        "ore_ont_7581.owl",
        "ore_ont_13503.owl",
        "ore_ont_15703.owl",
    }:
        raise ValueError("unexpected Thing/Nothing collisions in the registry")
    for ontology, spec in SPECIAL_IRI_FIXED.items():
        direct_exact = direct_special_iri_exact_row(ontology, spec, direct_dir)
        selected[ontology] = direct_exact
        # Older local-name matches for these collision-bearing symbols do not
        # validate this fix. Keep only the fresh full-IRI route witness.
        exact_routes[ontology].clear()
        exact_routes[ontology][direct_exact["route"]] = float(
            direct_exact["wall_s"]
        )
    for ontology, spec in COMPLETED_INCORRECT.items():
        selected[ontology] = completed_incorrect_row(ontology, spec, direct_dir)

    selected.update(unresolved_rows(direct_dir))
    if set(selected) != set(grouped):
        missing = sorted(set(grouped) - set(selected), key=ontology_key)
        extra = sorted(set(selected) - set(grouped), key=ontology_key)
        raise ValueError(f"selection mismatch; missing={missing}, extra={extra}")

    output = []
    for ontology in sorted(selected, key=ontology_key):
        row = selected[ontology]
        alternatives = [
            route
            for route, _wall in sorted(
                exact_routes[ontology].items(), key=lambda item: (item[1], item[0])
            )
            if route != row["route"]
        ]
        row["other_verified_exact_routes"] = ",".join(alternatives)
        output.append(row)

    counts: dict[str, int] = defaultdict(int)
    for row in output:
        counts[row["state"]] += 1
        if row["state"] == "exact_gold":
            if row["within_limits"] != "yes":
                raise ValueError(f"exact row not within limits: {row['ontology']}")
            if float(row["wall_s"]) > TIMEOUT_S:
                raise ValueError(f"exact row exceeds time limit: {row['ontology']}")
            if float(row["peak_mb"]) > MEMORY_LIMIT_MB:
                raise ValueError(f"exact row exceeds memory limit: {row['ontology']}")
            for field in (
                "route",
                "binary_sha256",
                "binary_locator",
                "route_environment",
                "invocation",
                "gold_sha256",
                "signature_sha256",
                "evidence",
            ):
                if not row[field]:
                    raise ValueError(f"blank {field} for exact row {row['ontology']}")

    expected = {
        "exact_gold": 586,
        "completed_incorrect": 1,
        "adjudicated_correct_stale_gold": 2,
        "no_complete_within_limit_valid_gold": 1,
        "unresolved_no_authoritative_gold": 2,
    }
    if dict(counts) != expected:
        raise ValueError(f"unexpected state counts: {dict(counts)}")
    return output


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base-registry", required=True)
    parser.add_argument("--retained-evidence", required=True)
    parser.add_argument("--direct-validation", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    rows = build(args)
    output_path = Path(args.output)
    with output_path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {len(rows)} rows to {output_path}")


if __name__ == "__main__":
    main()
