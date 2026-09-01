#!/usr/bin/env python3
"""Fail closed unless one benchmark result and its evidence are resumable."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


TERMINAL = {
    "ok", "timeout", "memout", "error", "unsupported", "output_error",
    "fingerprint_error",
}


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--result", required=True, type=Path)
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--ontology-id", required=True)
    parser.add_argument("--ontology", required=True, type=Path)
    parser.add_argument("--input-ontology", type=Path)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--runner", required=True, type=Path)
    args = parser.parse_args()

    require(args.result.is_file(), "result is absent")
    require(args.ontology.is_file(), "ontology is absent")
    runtime_ontology = args.input_ontology or args.ontology
    require(runtime_ontology.is_file(), "runtime ontology serialization is absent")
    require(args.runtime.is_file(), "runtime is absent")
    require(args.runner.is_file(), "runner is absent")
    record = json.loads(args.result.read_text(encoding="utf-8"))
    require(record.get("schema") == 1, "wrong schema")
    require(record.get("baseline") == args.baseline, "wrong baseline")
    require(record.get("ontology_id") == args.ontology_id, "wrong ontology id")
    require(record.get("ontology_sha256") == digest(args.ontology), "ontology digest mismatch")
    # Native runners may classify a reasoner-specific serialization (Konclude)
    # rather than the canonical frozen ontology, so bind that runtime input
    # separately.  Java runners always receive args.ontology directly; their
    # ontology_sha256, command, runtime, and runner bindings already identify
    # the complete execution input and legacy Java records intentionally have
    # no redundant input_ontology_sha256 field.
    if args.baseline in {"km", "konclude"}:
        require(record.get("input_ontology_sha256") == digest(runtime_ontology),
                "runtime ontology serialization digest mismatch")
    runtime_key = "binary_sha256" if args.baseline in {"km", "konclude"} else "runtime_sha256"
    require(record.get(runtime_key) == digest(args.runtime), "runtime digest mismatch")
    require(record.get("runner_sha256") == digest(args.runner), "runner digest mismatch")
    require(record.get("status") in TERMINAL, "nonterminal or unknown status")
    require(record.get("checkpointed") is True, "result was not checkpointed")
    require(isinstance(record.get("wall_s"), (int, float)) and record["wall_s"] >= 0,
            "missing wall time")
    require(isinstance(record.get("peak_mb"), (int, float)) and record["peak_mb"] > 0,
            "missing peak RSS")
    require(isinstance(record.get("rc"), int), "missing final exit code")
    require(args.result.name.endswith(".result.json"), "unexpected result filename")
    stem = args.result.name[:-len(".result.json")]
    stderr = args.result.with_name(stem + ".stderr")
    require(stderr.is_file() and record.get("stderr_sha256") == digest(stderr),
            "stderr evidence mismatch")

    if record["status"] == "ok":
        require(record.get("consistency") in {True, False, "true", "false", "unknown"},
                "invalid consistency")
        require(isinstance(record.get("subsumptions"), int) and record["subsumptions"] >= 0,
                "invalid subsumption count")
        require(isinstance(record.get("unsatisfiable"), int) and record["unsatisfiable"] >= 0,
                "invalid unsatisfiable count")
        taxonomy = record.get("taxonomy_sha256", "")
        require(isinstance(taxonomy, str) and len(taxonomy) == 64, "invalid taxonomy digest")
        relation = record.get("relation_sha256", "")
        require(isinstance(relation, str) and len(relation) == 64, "invalid relation digest")
        output = Path(record.get("ontology", ""))  # overwritten below after structural check
        require(isinstance(record.get("output_sha256"), str), "missing output digest")
        candidates = list(args.result.parent.glob(stem + ".taxonomy.*"))
        candidates = [path for path in candidates if not path.name.endswith(".part")]
        require(len(candidates) == 1, "taxonomy output is absent or ambiguous")
        output = candidates[0]
        require(record["output_sha256"] == digest(output), "taxonomy output digest mismatch")
        fingerprint = args.result.with_name(stem + ".fingerprint.json")
        require(fingerprint.is_file(), "fingerprint receipt absent")
        fp = json.loads(fingerprint.read_text(encoding="utf-8"))
        require(fp.get("status") == "ok", "fingerprint receipt is not successful")
        require(fp.get("taxonomy_sha256") == taxonomy, "fingerprint taxonomy mismatch")
        require(fp.get("relation_sha256") == relation, "fingerprint relation mismatch")
        require(fp.get("input_sha256") == record["output_sha256"], "fingerprint input mismatch")
        if args.baseline == "konclude":
            require(fp.get("missing_source_declarations") == 0,
                    "Konclude taxonomy omits source class declarations")

    print(json.dumps({"status": "valid", "result": str(args.result),
                      "terminal_status": record["status"]}, sort_keys=True))


if __name__ == "__main__":
    main()
