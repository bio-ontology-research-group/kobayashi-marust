#!/usr/bin/env python3
"""Verify and atomically import the strict current-corpus final aggregate."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import shutil


BASELINES = ("km", "konclude", "hermit", "jfact", "openllet", "more", "elk", "whelk")
FINAL_FILES = (
    "current-aggregate.json",
    "current-disagreements.tsv",
    "current-results.tex",
    "result-records.sha256",
)
RECORD = re.compile(r"current-results/([^/]+)/([^/]+)\.result\.json")
TEX_DIGEST = re.compile(r"^% Generated from aggregate SHA-256 ([0-9a-f]{64})$")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest_manifest(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        fields = line.split("  ", 1)
        if len(fields) != 2 or not re.fullmatch(r"[0-9a-f]{64}", fields[0]):
            raise ValueError(f"malformed digest-manifest row: {line}")
        name = fields[1]
        if name in values:
            raise ValueError(f"duplicate digest-manifest path: {name}")
        values[name] = fields[0]
    return values


def verify(source: Path) -> dict:
    expected_names = set(FINAL_FILES)
    manifest = digest_manifest(source / "SHA256SUMS")
    if set(manifest) != expected_names:
        raise ValueError(f"unexpected final SHA256SUMS paths: {sorted(manifest)}")
    for name in FINAL_FILES:
        actual = digest(source / name)
        if actual != manifest[name]:
            raise ValueError(f"final digest mismatch for {name}: {actual}")

    aggregate = json.loads((source / "current-aggregate.json").read_text(encoding="utf-8"))
    if aggregate.get("schema") != 1 or aggregate.get("eligible_ontologies") != 189:
        raise ValueError("unexpected current aggregate identity")
    if aggregate.get("expected_runs") != 1512 or aggregate.get("missing_or_invalid_records") != 0:
        raise ValueError("current aggregate is incomplete")
    if aggregate.get("invalid_records") != []:
        raise ValueError("current aggregate retains invalid records")
    counts = aggregate.get("status_counts")
    if not isinstance(counts, dict) or set(counts) != set(BASELINES):
        raise ValueError("current aggregate baseline matrix differs")
    for baseline in BASELINES:
        if sum(counts[baseline].values()) != 189:
            raise ValueError(f"terminal statuses do not conserve 189 inputs: {baseline}")
    artifacts = aggregate.get("baseline_artifacts")
    bindings = aggregate.get("execution_bindings")
    if not isinstance(artifacts, dict) or set(artifacts) != set(BASELINES):
        raise ValueError("baseline artifact bindings are incomplete")
    if not isinstance(bindings, dict) or set(bindings) != set(BASELINES):
        raise ValueError("execution bindings are incomplete")

    record_manifest = digest_manifest(source / "result-records.sha256")
    if len(record_manifest) != 1512:
        raise ValueError(f"expected 1,512 result-record digests, found {len(record_manifest)}")
    by_baseline: dict[str, set[str]] = {baseline: set() for baseline in BASELINES}
    for name in record_manifest:
        match = RECORD.fullmatch(name)
        if not match or match.group(1) not in by_baseline:
            raise ValueError(f"unexpected result-record path: {name}")
        baseline, ontology = match.groups()
        if ontology in by_baseline[baseline]:
            raise ValueError(f"duplicate result-record index: {baseline}/{ontology}")
        by_baseline[baseline].add(ontology)
    ontology_sets = list(by_baseline.values())
    if any(len(values) != 189 for values in ontology_sets):
        raise ValueError("a baseline does not contain 189 unique result-record indexes")
    if any(values != ontology_sets[0] for values in ontology_sets[1:]):
        raise ValueError("baseline ontology index sets differ")

    tex_first = (source / "current-results.tex").read_text(encoding="utf-8").splitlines()[0]
    match = TEX_DIGEST.fullmatch(tex_first)
    aggregate_sha256 = manifest["current-aggregate.json"]
    if not match or match.group(1) != aggregate_sha256:
        raise ValueError("generated TeX is not bound to the final aggregate")
    with (source / "current-disagreements.tsv").open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        rows = list(reader)
        fieldnames = reader.fieldnames
    expected_header = {"ontology", "owl2dl", "relation_category", "relation_groups",
                       "consistency_category", "consistency_values"}
    if not rows and fieldnames is None:
        raise ValueError("missing disagreement TSV header")
    if set(fieldnames or ()) != expected_header:
        raise ValueError("unexpected disagreement TSV schema")
    names = [row["ontology"] for row in rows]
    if len(names) != len(set(names)) or not set(names).issubset(ontology_sets[0]):
        raise ValueError("disagreement rows are duplicated or outside the corpus")
    return {
        "schema": 1,
        "status": "verified",
        "aggregate_sha256": aggregate_sha256,
        "result_record_manifest_sha256": manifest["result-records.sha256"],
        "result_records": len(record_manifest),
        "ontologies": len(ontology_sets[0]),
        "baselines": list(BASELINES),
        "disagreements": len(rows),
    }


def import_final(source: Path, target: Path, tex_target: Path,
                 replace_existing: bool = False) -> dict:
    report = verify(source)
    if target.exists() and not replace_existing:
        raise ValueError(f"refusing to overwrite existing final import: {target}")
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = target.with_name(target.name + ".part")
    if temporary.exists():
        shutil.rmtree(temporary)
    temporary.mkdir()
    for name in (*FINAL_FILES, "SHA256SUMS"):
        shutil.copyfile(source / name, temporary / name)
    (temporary / "import-verification.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    previous = target.with_name(target.name + ".previous")
    if previous.exists():
        raise ValueError(f"stale replacement backup exists: {previous}")
    if target.exists():
        target.replace(previous)
    try:
        temporary.replace(target)
    except Exception:
        if previous.exists() and not target.exists():
            previous.replace(target)
        raise
    if previous.exists():
        shutil.rmtree(previous)
    tex_target.parent.mkdir(parents=True, exist_ok=True)
    tex_part = tex_target.with_name(tex_target.name + ".part")
    shutil.copyfile(target / "current-results.tex", tex_part)
    tex_part.replace(tex_target)
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--target", type=Path,
                        default=Path(__file__).resolve().parent / "generated" / "current-final")
    parser.add_argument("--tex-target", type=Path,
                        default=Path(__file__).resolve().parents[1] / "generated" / "current-results.tex")
    parser.add_argument("--verify-only", action="store_true")
    parser.add_argument("--replace-existing", action="store_true",
                        help="atomically replace an existing verified import")
    args = parser.parse_args()
    report = verify(args.source) if args.verify_only else import_final(
        args.source, args.target, args.tex_target, args.replace_existing)
    print(f"CURRENT_FINAL_IMPORT_OK\t{report['result_records']}\t{report['disagreements']}")


if __name__ == "__main__":
    main()
