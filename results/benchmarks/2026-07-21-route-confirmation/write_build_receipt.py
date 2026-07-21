#!/usr/bin/env python3
"""Write and validate the receipt for a byte-reproducible portable KM build."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def line_count(path: Path) -> int:
    with path.open("rb") as handle:
        return sum(1 for _ in handle)


def command_text(*command: str) -> str:
    completed = subprocess.run(
        command, check=True, text=True, capture_output=True
    )
    return completed.stdout.strip()


def glibc_versions(binary: Path) -> list[str]:
    text = command_text("/usr/bin/readelf", "--version-info", str(binary))
    versions = set(re.findall(r"GLIBC_(\d+\.\d+)", text))
    return sorted(versions, key=lambda value: tuple(map(int, value.split("."))))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-archive", type=Path, required=True)
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--build-input-archive", type=Path, required=True)
    parser.add_argument("--build-input-manifest", type=Path, required=True)
    parser.add_argument("--cargo-lock", type=Path, required=True)
    parser.add_argument("--container-image-ref", required=True)
    parser.add_argument("--container-image-digest", required=True)
    parser.add_argument("--container-image-id", required=True)
    parser.add_argument("--container-os-release", type=Path, required=True)
    parser.add_argument("--rustc-version", type=Path, required=True)
    parser.add_argument("--rustc-path", required=True)
    parser.add_argument("--rustc-sha256", required=True)
    parser.add_argument("--cargo-version", type=Path, required=True)
    parser.add_argument("--cargo-path", required=True)
    parser.add_argument("--cargo-sha256", required=True)
    parser.add_argument("--rustup-path", required=True)
    parser.add_argument("--rustup-sha256", required=True)
    parser.add_argument("--build-a", type=Path, required=True)
    parser.add_argument("--build-b", type=Path, required=True)
    parser.add_argument("--build-a-log", type=Path, required=True)
    parser.add_argument("--build-b-log", type=Path, required=True)
    parser.add_argument("--build-script", type=Path, required=True)
    parser.add_argument("--receipt-writer", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    paths = [
        args.source_archive,
        args.source_manifest,
        args.build_input_archive,
        args.build_input_manifest,
        args.cargo_lock,
        args.container_os_release,
        args.rustc_version,
        args.cargo_version,
        args.build_a,
        args.build_b,
        args.build_a_log,
        args.build_b_log,
        args.build_script,
        args.receipt_writer,
    ]
    missing = [str(path) for path in paths if not path.is_file()]
    if missing:
        raise SystemExit(f"missing build receipt inputs: {missing}")

    build_a_sha = sha256_file(args.build_a)
    build_b_sha = sha256_file(args.build_b)
    identical = build_a_sha == build_b_sha
    if not identical:
        raise SystemExit(
            f"clean builds differ: build-a={build_a_sha}, build-b={build_b_sha}"
        )

    versions = glibc_versions(args.build_a)
    receipt = {
        "schema_version": 1,
        "status": "verified_reproducible",
        "source": {
            "archive": args.source_archive.name,
            "archive_sha256": sha256_file(args.source_archive),
            "manifest": args.source_manifest.name,
            "manifest_sha256": sha256_file(args.source_manifest),
            "manifest_file_count": line_count(args.source_manifest),
            "cargo_lock_sha256": sha256_file(args.cargo_lock),
        },
        "build_input": {
            "archive": args.build_input_archive.name,
            "archive_sha256": sha256_file(args.build_input_archive),
            "manifest": args.build_input_manifest.name,
            "manifest_sha256": sha256_file(args.build_input_manifest),
            "manifest_file_count": line_count(args.build_input_manifest),
            "includes_vendored_dependencies": True,
        },
        "container": {
            "image_ref": args.container_image_ref,
            "image_digest": args.container_image_digest,
            "image_id": args.container_image_id,
            "os_release": args.container_os_release.read_text(
                encoding="utf-8", errors="replace"
            ),
        },
        "toolchain": {
            "rustc_version_verbose": args.rustc_version.read_text(
                encoding="utf-8", errors="replace"
            ).strip(),
            "rustc_path": args.rustc_path,
            "rustc_sha256": args.rustc_sha256,
            "cargo_version_verbose": args.cargo_version.read_text(
                encoding="utf-8", errors="replace"
            ).strip(),
            "cargo_path": args.cargo_path,
            "cargo_sha256": args.cargo_sha256,
            "rustup_path": args.rustup_path,
            "rustup_sha256": args.rustup_sha256,
        },
        "build": {
            "cargo_locked": True,
            "offline_vendored": True,
            "network_disabled": True,
            "jobs": 4,
            "cpus": 4,
            "memory_gib": 16,
            "source_date_epoch": 0,
            "command": [
                "cargo",
                "build",
                "--release",
                "--locked",
                "--offline",
                "-j4",
                "--bin",
                "km",
            ],
            "driver": args.build_script.name,
            "driver_sha256": sha256_file(args.build_script),
            "receipt_writer": args.receipt_writer.name,
            "receipt_writer_sha256": sha256_file(args.receipt_writer),
            "build_a_log": args.build_a_log.name,
            "build_a_log_sha256": sha256_file(args.build_a_log),
            "build_b_log": args.build_b_log.name,
            "build_b_log_sha256": sha256_file(args.build_b_log),
        },
        "outputs": {
            "build_a": args.build_a.name,
            "build_a_sha256": build_a_sha,
            "build_b": args.build_b.name,
            "build_b_sha256": build_b_sha,
            "binary_sha256": build_a_sha,
            "byte_identical": identical,
            "file": command_text("/usr/bin/file", "-b", str(args.build_a)),
            "glibc_versions": versions,
            "max_glibc": versions[-1] if versions else None,
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(args.output)
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
