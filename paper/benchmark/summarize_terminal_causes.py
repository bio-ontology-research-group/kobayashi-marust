#!/usr/bin/env python3
"""Produce a profile-aware, stderr-bound terminal-cause ledger."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path


def profile(path: Path) -> str:
    values: dict[str, bool] = {}
    terminal = False
    for raw in path.read_text(encoding="utf-8").splitlines():
        fields = raw.split("\t")
        if len(fields) == 4 and fields[0] == "P" and fields[1] in {"OWL2DL", "OWL2EL"}:
            values[fields[1]] = fields[2] == "true"
        elif fields == ["Z", "complete"]:
            terminal = True
    if not terminal or set(values) != {"OWL2DL", "OWL2EL"}:
        raise ValueError(f"incomplete profile {path}")
    if values["OWL2EL"]:
        return "OWL 2 EL"
    if values["OWL2DL"]:
        return "OWL 2 DL, non-EL"
    return "outside OWL 2 DL"


def cause(status: str, stderr: str) -> str:
    if status != "error":
        return status
    first = stderr.splitlines()[0] if stderr.splitlines() else ""
    if "complex class atom" in first:
        return "unsupported_complex_rule_atom"
    if "named role expected" in first and "ObjectInverseOf" in first:
        return "unsupported_inverse_role_position"
    if "worker engine exited -1" in first:
        return "route_no_retry_internal_cap"
    if "selected CB mechanism did not reach its complete fixpoint" in first:
        return "cb_incomplete_fixpoint"
    return "other_error"


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", required=True, type=Path)
    parser.add_argument("--profiles", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--array-job-id", required=True)
    parser.add_argument("--expected-count", type=int, default=189)
    parser.add_argument("--allow-incomplete", action="store_true")
    parser.add_argument("--output-tsv", required=True, type=Path)
    parser.add_argument("--output-json", required=True, type=Path)
    args = parser.parse_args()

    with args.manifest.open(encoding="utf-8", newline="") as stream:
        manifest_rows = list(csv.DictReader(stream, delimiter="\t"))
    expected = {row["id"] for row in manifest_rows if row.get("eligible") == "true"}
    if len(expected) != args.expected_count:
        raise ValueError(f"manifest population mismatch: {len(expected)}/{args.expected_count}")

    rows = []
    for result_path in sorted(args.results.glob("*.result.json")):
        record = json.loads(result_path.read_text(encoding="utf-8"))
        if record.get("slurm_array_job_id") != args.array_job_id:
            continue
        ontology = record.get("ontology_id")
        status = record.get("status")
        if not isinstance(ontology, str) or ontology not in expected:
            raise ValueError(f"unexpected ontology in {result_path}: {ontology!r}")
        if not isinstance(status, str) or status == "running":
            continue
        stderr_path = args.results / f"{ontology}.stderr"
        payload = stderr_path.read_bytes()
        expected_stderr = record.get("stderr_sha256")
        if expected_stderr != sha256(payload):
            raise ValueError(f"stderr digest mismatch for {ontology}")
        stderr = payload.decode("utf-8", errors="replace")
        rows.append({
            "ontology": ontology, "profile": profile(args.profiles / f"{ontology}.tsv"),
            "status": status, "cause": cause(status, stderr),
            "wall_s": record.get("wall_s", ""), "peak_mb": record.get("peak_mb", ""),
            "stderr_sha256": expected_stderr,
        })
    observed = {row["ontology"] for row in rows}
    if len(observed) != len(rows):
        raise ValueError("duplicate ontology in cause ledger")
    if observed != expected and not args.allow_incomplete:
        raise ValueError(f"refusing incomplete cause ledger: {len(rows)}/{len(expected)}")

    args.output_tsv.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(args.output_tsv) + ".part")
    with temporary.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=rows[0].keys(), delimiter="\t")
        writer.writeheader(); writer.writerows(rows)
    temporary.replace(args.output_tsv)
    counts = Counter((row["profile"], row["cause"]) for row in rows)
    summary = {
        "schema": 1, "array_job_id": args.array_job_id,
        "terminal_records": len(rows), "expected_records": len(expected),
        "complete": observed == expected,
        "missing_records": sorted(expected - observed),
        "counts": [
            {"profile": profile_name, "cause": cause_name, "count": count}
            for (profile_name, cause_name), count in sorted(counts.items())
        ],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(args.output_json) + ".part")
    temporary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(args.output_json)
    print(f"TERMINAL_CAUSES_OK\t{len(rows)}\t{len(counts)}")


if __name__ == "__main__":
    main()
