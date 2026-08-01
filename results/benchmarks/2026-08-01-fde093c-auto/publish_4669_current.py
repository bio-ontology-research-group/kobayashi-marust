#!/usr/bin/env python3
"""Publish the source-bound 4669 row after both full-IRI gates pass."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path


ROOT = Path("/ibex/scratch/hohndor/km/release-fde093c-auto-20260801")
BINARY_SHA = "0aa78e92d327c2e73570243388e43347abb199d1bef9d461c94302a1d5eff20b"
SCC_DIGEST = "a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30"
PAIR_DIGEST = "d02decbafe66d8a9f1afaf7385785b6937fe46c1f288a33113c83c2bbe805b96"
ORACLE_JOB = "49795051"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def atomic_json(path: Path, row: dict) -> None:
    temporary = path.with_name(f"{path.name}.tmp.{os.getpid()}")
    temporary.write_text(json.dumps(row, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def main() -> None:
    binary = ROOT / "km"
    checkpoint = ROOT / "results/ore_ont_4669.owl.checkpoint.json"
    result = ROOT / "results/ore_ont_4669.owl.json"
    oracle_log = ROOT / f"4669-oracle-{ORACLE_JOB}.out"
    old_fingerprint = ROOT / "old-4669-fingerprint.json"

    assert sha256(binary) == BINARY_SHA
    row = json.loads(checkpoint.read_text(encoding="utf-8"))
    assert row["binary_sha256"] == BINARY_SHA
    assert row["status"] == "ok" and row["rc"] == 0
    assert row["selected_route_trace"] == "mirror_private"
    assert row["fulliri_taxonomy_sha256"] == SCC_DIGEST
    assert row["fulliri_subsumptions"] == 846_306
    assert row["fulliri_unsatisfiable"] == 0

    old = json.loads(old_fingerprint.read_text(encoding="utf-8"))
    assert old["taxonomy_sha256"] == SCC_DIGEST
    assert old["subsumptions"] == 846_306 and old["unsatisfiable"] == 0

    oracle_text = oracle_log.read_text(encoding="utf-8")
    assert f"ORACLE_MATCH pairs=846306 unsat=0 digest={PAIR_DIGEST}" in oracle_text
    assert "TASK_COMPLETE ontology=ore_ont_4669.owl revision=fde093c" in oracle_text

    row.update(
        solved=True,
        verdict="nogold",
        correctness_basis="independent_fulliri_private_mirror_oracle",
        signature_kind="fulliri-oracle-v1",
        signature_sha256=PAIR_DIGEST,
        consistent=True,
        subsumptions=846_306,
        unsatisfiable=0,
        output_path=None,
        harness_adjudication={
            "generic_24g_job": "49793194_157",
            "generic_96g_job": "49793503_157",
            "generic_failure": (
                "local-name postprocessor reached 79.9 GiB; reasoner result "
                "was independently retained under its 20-GiB cap"
            ),
            "streaming_fulliri_job": "49794816_157",
            "streaming_fulliri_digest": SCC_DIGEST,
            "historical_output_streaming_digest": SCC_DIGEST,
            "oracle_job": ORACLE_JOB,
            "oracle_digest": PAIR_DIGEST,
            "oracle_kind": "independent-full-iri-v1",
            "oracle_verdict": "match",
        },
    )
    atomic_json(result, row)
    atomic_json(checkpoint, row)
    print(json.dumps(row, sort_keys=True))


if __name__ == "__main__":
    main()
