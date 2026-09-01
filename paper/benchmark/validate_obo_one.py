#!/usr/bin/env python3
"""Independently validate one acquired OBO artifact on a compute node."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("--index", type=int)
    args = parser.parse_args()
    index = args.index
    if index is None:
        index = int(os.environ["SLURM_ARRAY_TASK_ID"])
    with args.manifest.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    row = rows[index]
    record_path = args.snapshot / "records" / f"{row['id']}.json"
    record = json.loads(record_path.read_text(encoding="utf-8"))
    result: dict[str, object] = {
        "schema": 1, "id": row["id"], "index": index,
        "acquisition_record": str(record_path),
        "acquisition_status": record.get("status"),
    }
    if record.get("status") != "acquired":
        result["status"] = "source_unavailable"
    else:
        source = Path(str(record["path"]))
        if not source.is_file() or source.stat().st_size == 0:
            result["status"] = "missing_or_empty"
        elif source.stat().st_size != record.get("bytes"):
            result["status"] = "size_mismatch"
        else:
            actual = digest(source)
            result.update({"bytes": source.stat().st_size, "sha256": actual})
            if actual != record.get("sha256"):
                result["status"] = "digest_mismatch"
            else:
                with source.open("rb") as stream:
                    prefix = stream.read(4096).lstrip().lower()
                if prefix.startswith(b"<!doctype html") or prefix.startswith(b"<html"):
                    result["status"] = "html_response"
                else:
                    result["status"] = "verified"
    output_dir = args.snapshot / "validation"
    output_dir.mkdir(exist_ok=True)
    output = output_dir / f"{row['id']}.json"
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, sort_keys=True))
    if result["status"] not in {"verified", "source_unavailable"}:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
