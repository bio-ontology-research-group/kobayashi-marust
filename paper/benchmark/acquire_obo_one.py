#!/usr/bin/env python3
"""Acquire one OBO candidate in a Slurm array with fail-closed validation."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("output_root", type=Path)
    parser.add_argument("--index", type=int, default=None)
    args = parser.parse_args()

    with args.manifest.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    index = args.index
    if index is None:
        raw = os.environ.get("SLURM_ARRAY_TASK_ID")
        if raw is None:
            raise SystemExit("supply --index or SLURM_ARRAY_TASK_ID")
        index = int(raw)
    if index < 0 or index >= len(rows):
        raise SystemExit(f"index {index} outside 0..{len(rows)-1}")

    row = rows[index]
    identifier = row["id"]
    args.output_root.mkdir(parents=True, exist_ok=True)
    data = args.output_root / "sources"
    records = args.output_root / "records"
    data.mkdir(exist_ok=True)
    records.mkdir(exist_ok=True)
    destination = data / f"{identifier}.owl"
    temporary = destination.with_suffix(".owl.part")
    record_path = records / f"{identifier}.json"

    started = time.time()
    command = [
        "curl", "--location", "--fail-with-body", "--silent", "--show-error",
        "--retry", "2", "--retry-all-errors", "--connect-timeout", "30",
        "--max-time", "900", "--max-filesize", str(8 * 1024 * 1024 * 1024),
        "--output", str(temporary), "--write-out",
        "%{http_code}\t%{url_effective}\t%{content_type}\t%{size_download}",
        row["source_url"],
    ]
    completed = subprocess.run(command, text=True, capture_output=True)
    fields = completed.stdout.rsplit("\n", 1)[-1].split("\t") if completed.stdout else []
    record: dict[str, object] = {
        "schema": 1,
        "index": index,
        "id": identifier,
        "title": row["title"],
        "source_url": row["source_url"],
        "licence_url": row["licence_url"],
        "registry_sha256": row["registry_sha256"],
        "curl_exit_code": completed.returncode,
        "stderr": completed.stderr[-4000:],
        "elapsed_s": time.time() - started,
        "status": "download_error",
    }
    if len(fields) == 4:
        record.update(
            {
                "http_code": fields[0],
                "final_url": fields[1],
                "content_type": fields[2],
                "reported_size": fields[3],
            }
        )

    if completed.returncode == 0 and temporary.is_file():
        size = temporary.stat().st_size
        prefix = temporary.read_bytes()[:512].lstrip().lower()
        looks_html = prefix.startswith(b"<!doctype html") or prefix.startswith(b"<html")
        if size == 0:
            record["status"] = "empty"
        elif looks_html:
            record["status"] = "html_response"
        else:
            temporary.replace(destination)
            record.update(
                {
                    "status": "acquired",
                    "bytes": size,
                    "sha256": sha256(destination),
                    "path": str(destination),
                }
            )
    if temporary.exists():
        temporary.unlink()
    record_path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(record, sort_keys=True))
    if record["status"] != "acquired":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
