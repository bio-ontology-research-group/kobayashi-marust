#!/usr/bin/env python3
"""Join acquisition and independent validation into the frozen OBO corpus."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path


FIELDS = [
    "index", "id", "title", "activity_status", "eligible", "status",
    "source_url", "final_url", "licence_url", "repository", "bytes",
    "sha256", "content_type", "snapshot_date", "registry_sha256",
]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("candidates", type=Path)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("output_prefix", type=Path)
    args = parser.parse_args()
    with args.candidates.open(encoding="utf-8", newline="") as stream:
        candidates = list(csv.DictReader(stream, delimiter="\t"))
    if len(candidates) != 190 or len({row["id"] for row in candidates}) != 190:
        raise SystemExit("candidate manifest must contain 190 unique rows")
    frozen = []
    for index, candidate in enumerate(candidates):
        identifier = candidate["id"]
        acquisition = json.loads((args.snapshot / "records" / f"{identifier}.json").read_text())
        validation = json.loads((args.snapshot / "validation" / f"{identifier}.json").read_text())
        if acquisition["index"] != index or validation["index"] != index:
            raise SystemExit(f"index mismatch for {identifier}")
        eligible = validation["status"] == "verified" and bool(candidate["licence_url"].strip())
        frozen.append({
            "index": index,
            "id": identifier,
            "title": candidate["title"],
            "activity_status": candidate["activity_status"],
            "eligible": str(eligible).lower(),
            "status": validation["status"],
            "source_url": candidate["source_url"],
            "final_url": acquisition.get("final_url", ""),
            "licence_url": candidate["licence_url"],
            "repository": candidate["repository"],
            "bytes": acquisition.get("bytes", ""),
            "sha256": acquisition.get("sha256", ""),
            "content_type": acquisition.get("content_type", ""),
            "snapshot_date": candidate["snapshot_date"],
            "registry_sha256": candidate["registry_sha256"],
        })
    if sum(row["eligible"] == "true" for row in frozen) != 189:
        raise SystemExit("expected 189 independently verified eligible sources")
    args.output_prefix.parent.mkdir(parents=True, exist_ok=True)
    tsv = args.output_prefix.with_suffix(".tsv")
    with tsv.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS, delimiter="\t", lineterminator="\n")
        writer.writeheader(); writer.writerows(frozen)
    payload = {
        "schema": 1,
        "snapshot_date": candidates[0]["snapshot_date"],
        "candidate_count": len(frozen),
        "eligible_count": sum(row["eligible"] == "true" for row in frozen),
        "source_unavailable_count": sum(row["status"] == "source_unavailable" for row in frozen),
        "registry_sha256": candidates[0]["registry_sha256"],
        "tsv": str(tsv),
        "tsv_sha256": hashlib.sha256(tsv.read_bytes()).hexdigest(),
    }
    args.output_prefix.with_suffix(".json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, sort_keys=True))


if __name__ == "__main__":
    main()
