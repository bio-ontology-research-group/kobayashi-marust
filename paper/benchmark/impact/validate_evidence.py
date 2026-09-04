#!/usr/bin/env python3
"""Fail closed on the compact practical-impact evidence bundle."""

from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path


PAPER = Path(__file__).resolve().parents[2]
IMPACT = PAPER / "impact"
EVIDENCE = IMPACT / "evidence"
CASES = IMPACT / "cases"
SOURCE_COMMIT = "301d37426cdf3dea249d9609037a2f1e47e89314"
BINARY = "c8688f6b286db2b422f1ec1df0874eadbbce0cc9e2899f35dbe143ccad70639d"
ELK = "7ffc442f2966667a488479a748502276136445c8e44ffd9e8498873a401cb3d4"
HERMIT = "59a7dc34d874c0dd9fb752594eb8d55b611e70d3cf7e839d581d7c366a5dd99c"
EMPTY = hashlib.sha256(b"").hexdigest()


def rows(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        parsed = list(csv.DictReader(stream, delimiter="\t"))
    if any(None in row or any(value is None for value in row.values()) for row in parsed):
        raise ValueError(f"malformed TSV row: {path}")
    return parsed


def receipt(path: Path) -> dict[str, str]:
    parsed: dict[str, str] = {}
    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if len(row) >= 2 and row[0].strip():
                if row[0] in parsed:
                    raise ValueError(f"duplicate receipt key {row[0]!r}: {path}")
                parsed[row[0]] = row[1]
    return parsed


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def logical_axioms(path: Path) -> set[str]:
    return {
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
        and not line.startswith("Prefix(")
        and not line.startswith("Ontology(")
        and line.strip() != ")"
    }


def require_exact_set(actual: set[str], expected: set[str], label: str) -> None:
    if actual != expected:
        raise ValueError(
            f"{label} set mismatch: missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )


def validate_cases() -> dict[str, str]:
    expected_hashes = {
        "hidden-full-dl-negative": "5f5ff4e146aa806173be68ccb91f6ba3117c9c8b09ae00304591480d69095d2f",
        "hidden-full-dl-positive": "8fd5edecf594143e058b16af4bb3b534a30bbbe03253570010e4d0574cf6c8bd",
        "snomed-style-negative": "116e6ef80409473305b640ea5fe8d5307af4277fb2e36e3d65390a0e5ad96133",
        "snomed-style-positive": "ab3838cfcc5412077e770dec74b73743dc4d255a077f3cee55f7835b827a6afc",
        "access-control-negative": "ec8f45a9374f81201ecbb93da9ed604bf6d74ce95ae67ed450d14db6bc85075f",
        "access-control-positive": "47929faf01d0e8e0de87d380bd5b1efcbe0ccf3a9bb13dd09e8dbc339bf2deff",
    }
    require_exact_set(
        {path.stem for path in CASES.glob("*.ofn")}, set(expected_hashes), "case"
    )
    for name, digest in expected_hashes.items():
        if sha256(CASES / f"{name}.ofn") != digest:
            raise ValueError(f"controlled case digest changed: {name}")

    pairs = {
        "hidden-full-dl": (
            "SubClassOf(:IntegratedFinding ObjectSomeValuesFrom(:hasParticipant :PathologicalProcess))",
            "SubClassOf(:IntegratedFinding ObjectSomeValuesFrom(:hasParticipant :AnatomicalStructure))",
        ),
        "access-control": (
            "SubClassOf(:PrivilegedContractor ObjectSomeValuesFrom(:hasClearance :HighClearance))",
            "SubClassOf(:PrivilegedContractor ObjectSomeValuesFrom(:hasClearance :LowClearance))",
        ),
    }
    for stem, (conflict, control) in pairs.items():
        positive = logical_axioms(CASES / f"{stem}-positive.ofn")
        negative = logical_axioms(CASES / f"{stem}-negative.ofn")
        if positive - negative != {conflict} or negative - positive != {control}:
            raise ValueError(f"{stem} is no longer a one-axiom repaired pair")

    positive = logical_axioms(CASES / "snomed-style-positive.ofn")
    negative = logical_axioms(CASES / "snomed-style-negative.ofn")
    maximum = "SubClassOf(:BilateralProcedure ObjectMaxCardinality(1 :hasLaterality owl:Thing))"
    if positive - negative != {maximum} or negative - positive:
        raise ValueError("SNOMED-style control must differ only by maximum cardinality")
    required_tbox = {
        "DisjointClasses(:LeftLaterality :RightLaterality)",
        "SubClassOf(:BilateralProcedure ObjectSomeValuesFrom(:hasLaterality :LeftLaterality))",
        "SubClassOf(:BilateralProcedure ObjectSomeValuesFrom(:hasLaterality :RightLaterality))",
        maximum,
    }
    if not required_tbox <= positive:
        raise ValueError("SNOMED-style TBox incoherence pattern changed")
    if "ClassAssertion(:BilateralProcedure :exampleCase)" not in positive:
        raise ValueError("SNOMED-style ABox inconsistency trigger missing")

    expected_labels = {
        "hidden-full-dl-negative": "biomedical merge repaired control",
        "hidden-full-dl-positive": "biomedical merge conflict",
        "snomed-style-negative": "SNOMED-style consistent control",
        "snomed-style-positive": "SNOMED-style inconsistent ABox",
        "access-control-negative": "access-policy repaired control",
        "access-control-positive": "access-policy conflict",
    }
    case_map = {row["legacy_id"]: row["publication_label"] for row in rows(IMPACT / "case-map.tsv")}
    if case_map != expected_labels:
        raise ValueError(f"case-map labels changed: {case_map}")
    return expected_hashes


def validate_km_classifications(case_hashes: dict[str, str]) -> dict[str, dict[str, str]]:
    expected = {
        "hidden-full-dl-negative": ("True", "0", "1"),
        "hidden-full-dl-positive": ("True", "1", "0"),
        "snomed-style-negative": ("True", "0", "1"),
        "snomed-style-positive": ("False", "0", "0"),
        "access-control-negative": ("True", "0", "1"),
        "access-control-positive": ("True", "1", "0"),
        "galen-ore9724": ("True", "0", "457090"),
        "galen-ore9724-repeat": ("True", "0", "457090"),
    }
    receipt_dir = EVIDENCE / "receipts"
    parsed = {
        name: receipt(receipt_dir / f"{name}.receipt.tsv") for name in expected
    }
    fingerprint_dir = EVIDENCE / "fingerprints"
    require_exact_set(
        {path.name.removesuffix(".fingerprint.json") for path in fingerprint_dir.glob("*.json")},
        set(expected),
        "fingerprint",
    )
    for name, wanted in expected.items():
        row = parsed[name]
        if row.get("status") != "ok" or row.get("exit_code") != "0":
            raise ValueError(f"KM success receipt is not successful: {name}")
        if row.get("source_commit") != SOURCE_COMMIT or row.get("binary_sha256") != BINARY:
            raise ValueError(f"KM source or binary binding changed: {name}")
        actual = (row.get("consistent"), row.get("unsatisfiable"), row.get("subsumptions"))
        if actual != wanted:
            raise ValueError(f"KM result changed for {name}: {actual} != {wanted}")
        if name in case_hashes and row.get("ontology_sha256") != case_hashes[name]:
            raise ValueError(f"KM ontology binding changed: {name}")
        fingerprint_path = fingerprint_dir / f"{name}.fingerprint.json"
        if sha256(fingerprint_path) != row.get("fingerprint_sha256"):
            raise ValueError(f"fingerprint digest mismatch: {name}")
        value = json.loads(fingerprint_path.read_text(encoding="utf-8"))
        fp_actual = (str(value["consistent"]), str(value["unsatisfiable"]), str(value["subsumptions"]))
        if fp_actual != wanted:
            raise ValueError(f"fingerprint values changed for {name}: {fp_actual}")
        if value["input_sha256"] != row["output_sha256"]:
            raise ValueError(f"fingerprint is not bound to receipt output: {name}")
        if value["source_ontology_sha256"] != row["ontology_sha256"]:
            raise ValueError(f"fingerprint is not bound to receipt ontology: {name}")

    for field in ("taxonomy_sha256", "relation_sha256"):
        if parsed["galen-ore9724"][field] != parsed["galen-ore9724-repeat"][field]:
            raise ValueError(f"GALEN repeats disagree on {field}")
    return parsed


def validate_uberon_failures() -> None:
    receipt_dir = EVIDENCE / "receipts"
    expected = {
        "uberon-2026-06-23": ("1", "17724884"),
        "uberon-2026-06-23-repeat": ("1", "17604952"),
        "uberon-production_all1": ("124", "577736"),
        "uberon-certified_nominals": ("124", "3146808"),
    }
    uberon_sha = "13579e2a9760969bb07beaf4701d019a90c5f63556bd593685ed876c44a8aa93"
    for name, (exit_code, peak_kib) in expected.items():
        row = receipt(receipt_dir / f"{name}.receipt.tsv")
        if row.get("status") != "error" or row.get("exit_code") != exit_code:
            raise ValueError(f"Uberon failure unexpectedly changed: {name}")
        if row.get("binary_sha256") != BINARY or row.get("ontology_sha256") != uberon_sha:
            raise ValueError(f"Uberon failure binding changed: {name}")
        text = (receipt_dir / f"{name}.receipt.tsv").read_text(encoding="utf-8")
        if f"Maximum resident set size (kbytes): {peak_kib}" not in text:
            raise ValueError(f"Uberon peak RSS changed: {name}")
        if name.startswith("uberon-2026") and row.get("output_sha256") != EMPTY:
            raise ValueError(f"failed automatic Uberon run has nonempty output digest: {name}")
        if (EVIDENCE / "fingerprints" / f"{name}.fingerprint.json").exists():
            raise ValueError(f"failed Uberon run must not have a fingerprint: {name}")


def validate_explanations(case_hashes: dict[str, str]) -> None:
    expected = {
        "hidden-full-dl-positive": {
            "query": {"type": "unsatisfiable", "class": "http://example.org/impact#IntegratedFinding"},
            "axioms": {
                "DisjointClasses(:AnatomicalStructure :PathologicalProcess)",
                "SubClassOf(:ExternalFinding ObjectAllValuesFrom(:hasParticipant :AnatomicalStructure))",
                "SubClassOf(:IntegratedFinding :ExternalFinding)",
                "SubClassOf(:IntegratedFinding ObjectSomeValuesFrom(:hasParticipant :PathologicalProcess))",
            },
        },
        "access-control-positive": {
            "query": {"type": "unsatisfiable", "class": "http://example.org/impact#PrivilegedContractor"},
            "axioms": {
                "DisjointClasses(:LowClearance :HighClearance)",
                "SubClassOf(:Contractor ObjectAllValuesFrom(:hasClearance :LowClearance))",
                "SubClassOf(:PrivilegedContractor :Contractor)",
                "SubClassOf(:PrivilegedContractor ObjectSomeValuesFrom(:hasClearance :HighClearance))",
            },
        },
        "snomed-style-positive": {
            "query": {"type": "inconsistent"},
            "axioms": {
                "DisjointClasses(:LeftLaterality :RightLaterality)",
                "SubClassOf(:BilateralProcedure ObjectSomeValuesFrom(:hasLaterality :LeftLaterality))",
                "SubClassOf(:BilateralProcedure ObjectSomeValuesFrom(:hasLaterality :RightLaterality))",
                "SubClassOf(:BilateralProcedure ObjectMaxCardinality(1 :hasLaterality owl:Thing))",
                "ClassAssertion(:BilateralProcedure :exampleCase)",
            },
        },
    }
    explanation_dir = EVIDENCE / "explanations"
    require_exact_set(
        {path.name.removesuffix(".explain.json") for path in explanation_dir.glob("*.json")},
        set(expected),
        "explanation",
    )
    for name, wanted in expected.items():
        path = explanation_dir / f"{name}.explain.json"
        value = json.loads(path.read_text(encoding="utf-8"))
        if value.get("status") != "entailed" or value.get("query") != wanted["query"]:
            raise ValueError(f"explanation query or status changed: {name}")
        if value.get("enumerationComplete") is not False or value.get("limitReached") is not True:
            raise ValueError(f"explanation bounds no longer explicit: {name}")
        supports = value.get("justifications")
        if not isinstance(supports, list) or len(supports) != 1:
            raise ValueError(f"expected exactly one bounded support: {name}")
        support = supports[0]
        if support.get("verified") is not True or support.get("subsetMinimal") is not True:
            raise ValueError(f"explanation support lost oracle verification: {name}")
        actual_axioms = {item["functionalSyntax"] for item in support["axioms"]}
        if actual_axioms != wanted["axioms"]:
            raise ValueError(f"explanation support changed: {name}")
        rec = receipt(EVIDENCE / "receipts" / f"{name}.explain.receipt.tsv")
        if rec.get("exit_code") != "0" or rec.get("binary_sha256") != BINARY:
            raise ValueError(f"explanation receipt failed or changed binary: {name}")
        if rec.get("ontology_sha256") != case_hashes[name] or rec.get("output_sha256") != sha256(path):
            raise ValueError(f"explanation receipt binding changed: {name}")


def validate_baselines(case_hashes: dict[str, str]) -> None:
    expected_cases = set(case_hashes)
    expected_cases.discard("galen-ore9724")
    expected_cases.discard("galen-ore9724-repeat")
    expected = {
        "hidden-full-dl-negative": ("true", 0, 1),
        "hidden-full-dl-positive": ("true", 1, 0),
        "snomed-style-negative": ("true", 0, 1),
        "snomed-style-positive": ("false", 0, 0),
        "access-control-negative": ("true", 0, 1),
        "access-control-positive": ("true", 1, 0),
    }
    for system, runtime in (("elk", ELK), ("hermit", HERMIT)):
        directory = EVIDENCE / "baselines" / system
        actual_cases = {path.name.removesuffix(".result.json") for path in directory.glob("*.json")}
        require_exact_set(actual_cases, expected_cases, f"{system} baseline")
        values: dict[str, dict[str, object]] = {}
        for name in sorted(expected_cases):
            value = json.loads((directory / f"{name}.result.json").read_text(encoding="utf-8"))
            values[name] = value
            if value.get("status") != "ok" or value.get("rc") != 0:
                raise ValueError(f"baseline did not complete: {system}/{name}")
            if value.get("runtime_sha256") != runtime or value.get("ontology_sha256") != case_hashes[name]:
                raise ValueError(f"baseline binding changed: {system}/{name}")
            wanted = ("true", 0, 1) if system == "elk" else expected[name]
            actual = (value.get("consistency"), value.get("unsatisfiable"), value.get("subsumptions"))
            if actual != wanted:
                raise ValueError(f"baseline outcome changed: {system}/{name}: {actual}")
        if system == "elk":
            for stem in ("hidden-full-dl", "snomed-style", "access-control"):
                positive = values[f"{stem}-positive"]
                negative = values[f"{stem}-negative"]
                if positive["relation_sha256"] != negative["relation_sha256"]:
                    raise ValueError(f"ELK unexpectedly distinguishes controlled pair: {stem}")


def validate_ledgers() -> None:
    ledger = rows(IMPACT / "ledger.tsv")
    expected_states = {
        "BIO-UBERON": "failed",
        "BIO-GALEN-ORE": "executed",
        "BIO-GALEN-CURRENT-BIOPORTAL": "blocked",
        "BIO-UNMIREOT-CONTROL": "executed",
        "BIO-UNMIREOT-REPLICATION": "proposed",
        "BIO-SNOMED-SYNTH": "executed",
        "BIO-SNOMED-LICENSED": "blocked",
        "NONBIO-ACCESS": "executed",
        "NONBIO-CONFIG": "proposed",
        "NONBIO-DATA-GOV": "proposed",
    }
    actual_states = {row["id"]: row["evidence_state"] for row in ledger}
    if actual_states != expected_states:
        raise ValueError(f"impact ledger states changed: {actual_states}")
    snomed = next(row for row in ledger if row["id"] == "BIO-SNOMED-SYNTH")
    if "does not directly publish a TBox-only" not in snomed["not_demonstrated_or_remaining"]:
        raise ValueError("SNOMED-style TBox/ABox evidence boundary is missing")
    results = rows(EVIDENCE / "results.tsv")
    indexed = {row["evidence_id"]: row for row in results}
    summary_expectations = {
        "KM-HIDDEN-CONTROL": ("success", "true", "0", "1"),
        "KM-HIDDEN-CONFLICT": ("success", "true", "1", "0"),
        "KM-SNOMED-CONTROL": ("success", "true", "0", "1"),
        "KM-SNOMED-ABOX": ("success", "false", "0", "0"),
        "KM-ACCESS-CONTROL": ("success", "true", "0", "1"),
        "KM-ACCESS-CONFLICT": ("success", "true", "1", "0"),
        "KM-GALEN-1": ("success", "true", "0", "457090"),
        "KM-GALEN-2": ("success", "true", "0", "457090"),
        "KM-UBERON-AUTO-1": ("failure", "NA", "NA", "NA"),
        "KM-UBERON-AUTO-2": ("failure", "NA", "NA", "NA"),
        "KM-UBERON-PROD1": ("failure", "NA", "NA", "NA"),
        "KM-UBERON-NOMINALS": ("failure", "NA", "NA", "NA"),
        "KM-HIDDEN-EXPLAIN": ("success", "NA", "NA", "NA"),
        "KM-SNOMED-EXPLAIN": ("success", "NA", "NA", "NA"),
        "KM-ACCESS-EXPLAIN": ("success", "NA", "NA", "NA"),
        "ELK-HIDDEN-CONTROL": ("success-out-of-profile", "true", "0", "1"),
        "ELK-HIDDEN-CONFLICT": ("success-out-of-profile", "true", "0", "1"),
        "ELK-SNOMED-CONTROL": ("success-out-of-profile", "true", "0", "1"),
        "ELK-SNOMED-ABOX": ("success-out-of-profile", "true", "0", "1"),
        "ELK-ACCESS-CONTROL": ("success-out-of-profile", "true", "0", "1"),
        "ELK-ACCESS-CONFLICT": ("success-out-of-profile", "true", "0", "1"),
        "HERMIT-HIDDEN-CONTROL": ("success", "true", "0", "1"),
        "HERMIT-HIDDEN-CONFLICT": ("success", "true", "1", "0"),
        "HERMIT-SNOMED-CONTROL": ("success", "true", "0", "1"),
        "HERMIT-SNOMED-ABOX": ("success", "false", "0", "0"),
        "HERMIT-ACCESS-CONTROL": ("success", "true", "0", "1"),
        "HERMIT-ACCESS-CONFLICT": ("success", "true", "1", "0"),
    }
    require_exact_set(set(indexed), set(summary_expectations), "results ledger")
    for evidence_id, expected in summary_expectations.items():
        row = indexed[evidence_id]
        actual = (
            row["terminal_status"], row["consistent"],
            row["unsatisfiable_named"], row["subsumptions"],
        )
        if actual != expected:
            raise ValueError(f"results summary changed: {evidence_id}: {actual}")
    for row in results:
        evidence = EVIDENCE / row["evidence_file"]
        if not evidence.is_file():
            raise ValueError(f"results ledger points to missing evidence: {evidence}")
    jobs = {row["job_or_array"]: row for row in rows(EVIDENCE / "jobs.tsv")}
    expected_jobs = {
        "51298212": ("build", "1", "1", "success"),
        "51298364": ("controlled KM classification", "6", "4", "success"),
        "51298365": ("GALEN and Uberon KM classification", "4", "4", "mixed"),
        "51298402": ("explanation first attempt", "3", "2", "failure"),
        "51298706": ("explanation corrected rerun", "3", "2", "success"),
        "51298713": ("ELK and HermiT controlled baselines", "12", "4", "success"),
        "51298728": ("Uberon diagnostic routes", "2", "2", "failure"),
    }
    require_exact_set(set(jobs), set(expected_jobs), "job ledger")
    for job_id, expected in expected_jobs.items():
        row = jobs[job_id]
        actual = (row["stage"], row["tasks"], row["max_simultaneous"], row["terminal_state"])
        if actual != expected:
            raise ValueError(f"job summary changed: {job_id}: {actual}")
    if max(int(row["max_simultaneous"]) for row in jobs.values()) > 4:
        raise ValueError("impact job ledger exceeds four simultaneous tasks")


def validate_sources() -> None:
    sources = {row["id"]: row for row in rows(IMPACT / "sources.tsv")}
    expected = {
        "slater2020": ("2020-12-15", "DOI:10.1186/s12911-020-01336-2"),
        "unmireot": ("2020-12-04", "e579133d34b6e579da2b673f9cd0ffe0c8427fec"),
        "uberon-source": ("VersionIRI 2026-06-19; retrieved 2026-08-30", "938f51e7c3fc9fcbe5a2863eb346da8033737e568af5836958891c4c6bfb1192"),
        "uberon-merged": ("2026-08-30 paper snapshot", "13579e2a9760969bb07beaf4701d019a90c5f63556bd593685ed876c44a8aa93"),
        "galen-ore9724": ("ORE 2015 frozen corpus", "00c80e07aa57578c168d15a1755b62fde41c53dd69a2f04cc5d88c888c8baf19"),
        "galen-current": ("planned 2026-08-30 snapshot", "NOT_ACQUIRED"),
        "snomed-required": ("user-supplied licensed release", "INPUT_REQUIRED"),
        "km-impact-binary": ("v1.3.0-64-g301d374", BINARY),
        "elk-impact-baseline": ("0.6.0", ELK),
        "hermit-impact-baseline": ("1.4.5.519", HERMIT),
    }
    require_exact_set(set(sources), set(expected), "source ledger")
    for source_id, wanted in expected.items():
        actual = (sources[source_id]["version_or_date"], sources[source_id]["sha256_or_identity"])
        if actual != wanted:
            raise ValueError(f"source identity changed: {source_id}: {actual}")


def validate_manifest() -> None:
    manifest = EVIDENCE / "SHA256SUMS"
    listed: set[Path] = set()
    for line in manifest.read_text(encoding="utf-8").splitlines():
        digest, relative = line.split("  ", 1)
        path = EVIDENCE / relative
        if path in listed:
            raise ValueError(f"duplicate manifest path: {relative}")
        listed.add(path)
        if not path.is_file() or sha256(path) != digest:
            raise ValueError(f"manifest mismatch: {relative}")
    expected = {
        path for path in EVIDENCE.rglob("*")
        if path.is_file() and path != manifest and "__pycache__" not in path.parts
    }
    if listed != expected:
        raise ValueError(
            f"manifest coverage mismatch: missing={sorted(map(str, expected - listed))}, "
            f"extra={sorted(map(str, listed - expected))}"
        )


def main() -> None:
    expected_receipts = {
        "hidden-full-dl-negative", "hidden-full-dl-positive",
        "snomed-style-negative", "snomed-style-positive",
        "access-control-negative", "access-control-positive",
        "galen-ore9724", "galen-ore9724-repeat",
        "hidden-full-dl-positive.explain", "snomed-style-positive.explain",
        "access-control-positive.explain", "uberon-2026-06-23",
        "uberon-2026-06-23-repeat", "uberon-production_all1",
        "uberon-certified_nominals",
    }
    require_exact_set(
        {
            path.name.removesuffix(".receipt.tsv")
            for path in (EVIDENCE / "receipts").glob("*.receipt.tsv")
        },
        expected_receipts,
        "receipt",
    )
    build = receipt(EVIDENCE / "build-receipt.tsv")
    expected_build = {
        "source_commit": SOURCE_COMMIT,
        "binary_sha256": BINARY,
        "rustc": "rustc 1.96.0 (ac68faa20 2026-05-25)",
        "cargo": "cargo 1.96.0 (30a34c682 2026-05-25)",
        "host": "cn512-26-r",
        "slurm_job_id": "51298212",
    }
    if build != expected_build:
        raise ValueError("build receipt source or binary binding changed")
    case_hashes = validate_cases()
    validate_km_classifications(case_hashes)
    validate_uberon_failures()
    validate_explanations(case_hashes)
    validate_baselines(case_hashes)
    validate_ledgers()
    validate_sources()
    validate_manifest()
    print("IMPACT_EVIDENCE_OK\t8 KM classifications\t4 KM failures\t3 explanations\t12 baselines")


if __name__ == "__main__":
    main()
