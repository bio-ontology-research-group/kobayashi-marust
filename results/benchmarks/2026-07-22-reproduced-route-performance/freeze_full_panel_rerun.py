#!/usr/bin/env python3
"""Freeze the exact committed driver capsule for the 30-task ORE rerun."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess


DATED = Path("results/benchmarks/2026-07-22-reproduced-route-performance")
DRIVER_FILES = (
    DATED / "FullIriHermitOracle.java",
    DATED / "aggregate_full_panel.py",
    DATED / "full_panel_chunks.py",
    DATED / "full_panel_contract.py",
    DATED / "full_panel_fingerprint.py",
    DATED / "full_panel_run_one.py",
    DATED / "full_panel_run_one_fulliri_only.py",
    DATED / "ibex_aggregate_full_panel_chunked.sbatch",
    DATED / "ibex_build_full_panel.sbatch",
    DATED / "ibex_build_full_panel_rerun.sbatch",
    DATED / "ibex_full_panel_chunked_array.sbatch",
    DATED / "ontology-route-performance.pre-panel.tsv",
    DATED / "run_full_panel_ontology.py",
    DATED / "rustdl_json_adapter.py",
    DATED / "sequoia_json_adapter.py",
    DATED / "test_full_panel_chunks.py",
    Path("results/benchmarks/audit_full_panel_route_coverage.py"),
    Path("results/benchmarks/full_panel_correctness.py"),
    Path("results/benchmarks/test_audit_full_panel_route_coverage.py"),
    Path("results/benchmarks/test_full_panel_correctness.py"),
    Path("oracle/ore/ore_canon.py"),
    Path("oracle/ore/tree_watchdog.py"),
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def git_output(repository: Path, *arguments: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repository), *arguments], text=True
    ).strip()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repository = args.repository.resolve(strict=True)
    destination = args.destination.resolve(strict=False)
    if destination.exists():
        raise SystemExit(f"refusing pre-existing capsule destination: {destination}")
    if git_output(repository, "status", "--porcelain"):
        raise SystemExit("refusing to freeze a dirty repository")
    revision = git_output(repository, "rev-parse", "--verify", "HEAD")
    if len(revision) != 40:
        raise SystemExit(f"invalid repository revision: {revision!r}")

    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.parent / f".{destination.name}.tmp.{os.getpid()}"
    if temporary.exists():
        raise SystemExit(f"refusing pre-existing temporary capsule: {temporary}")
    temporary.mkdir()
    copied = []
    try:
        destination_names = [path.name for path in DRIVER_FILES]
        if len(destination_names) != len(set(destination_names)):
            raise SystemExit("driver capsule has duplicate flat destination names")
        for relative in DRIVER_FILES:
            source = repository / relative
            if not source.is_file():
                raise SystemExit(f"missing driver source: {source}")
            subprocess.run(
                ["git", "-C", str(repository), "ls-files", "--error-unmatch", str(relative)],
                check=True,
                stdout=subprocess.DEVNULL,
            )
            target = temporary / relative.name
            shutil.copy2(source, target)
            copied.append(
                {
                    "source": str(relative),
                    "file": target.name,
                    "sha256": sha256_file(target),
                }
            )
        source_receipt = temporary / "driver-source.json"
        source_receipt.write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "repository_revision": revision,
                    "files": copied,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        manifest_entries = [
            (path.name, sha256_file(path))
            for path in temporary.iterdir()
            if path.is_file() and path.name != "driver-files.sha256"
        ]
        manifest = temporary / "driver-files.sha256"
        manifest.write_text(
            "".join(
                f"{digest}  {name}\n"
                for name, digest in sorted(manifest_entries)
            ),
            encoding="utf-8",
        )
        temporary.replace(destination)
    except BaseException:
        shutil.rmtree(temporary, ignore_errors=True)
        raise

    print(
        json.dumps(
            {
                "destination": str(destination),
                "repository_revision": revision,
                "file_count": len(copied) + 1,
                "manifest": str(destination / "driver-files.sha256"),
                "manifest_sha256": sha256_file(destination / "driver-files.sha256"),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
