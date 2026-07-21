#!/usr/bin/env python3
"""Bind a reproducible KM capsule's source bytes to an exact Git commit."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--capsule", type=Path, required=True)
    parser.add_argument("--expected-git-archive-sha256", required=True)
    parser.add_argument("--retained-source-archive", type=Path)
    parser.add_argument("--expected-retained-source-archive-sha256")
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def run_git(repo: Path, *arguments: str, binary: bool = False):
    completed = subprocess.run(
        ["/usr/bin/git", "-C", str(repo), *arguments],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return completed.stdout if binary else completed.stdout.decode().strip()


def parse_manifest(path: Path) -> dict[str, str]:
    entries: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        digest, separator, relative = line.partition("  ")
        if not separator or len(digest) != 64 or relative in entries:
            raise ValueError(f"invalid source manifest line: {line!r}")
        entries[relative] = digest
    return entries


def tar_hashes(fileobj, mode: str) -> dict[str, str]:
    entries: dict[str, str] = {}
    with tarfile.open(fileobj=fileobj, mode=mode) as archive:
        for member in archive:
            if member.isdir():
                continue
            if not member.isfile():
                raise ValueError(f"non-regular source archive member: {member.name}")
            relative = member.name.removeprefix("./")
            if relative in entries:
                raise ValueError(f"duplicate source archive member: {relative}")
            extracted = archive.extractfile(member)
            if extracted is None:
                raise ValueError(f"cannot read source archive member: {relative}")
            entries[relative] = sha256_bytes(extracted.read())
    return entries


def main() -> int:
    args = parse_args()
    repo = args.repo.resolve()
    capsule = args.capsule.resolve()
    commit = run_git(repo, "rev-parse", f"{args.commit}^{{commit}}")
    if commit != args.commit:
        raise SystemExit(f"commit did not resolve exactly: {commit}")
    tree = run_git(repo, "show", "-s", "--format=%T", commit)
    timestamp = int(run_git(repo, "show", "-s", "--format=%ct", commit))
    repository = run_git(repo, "remote", "get-url", "origin")
    git_archive = run_git(
        repo,
        "archive",
        "--format=tar",
        commit,
        "engine",
        "tests",
        binary=True,
    )
    git_archive_sha256 = sha256_bytes(git_archive)
    if git_archive_sha256 != args.expected_git_archive_sha256:
        raise SystemExit(
            "git archive differs: expected "
            f"{args.expected_git_archive_sha256}, observed {git_archive_sha256}"
        )

    retained_source_archive_sha256 = ""
    retained_git_archive_sha256 = ""
    retained_archive_checks = {}
    retained_options = (
        args.retained_source_archive,
        args.expected_retained_source_archive_sha256,
    )
    if any(value is not None for value in retained_options) and not all(
        value is not None for value in retained_options
    ):
        raise SystemExit(
            "retained source archive and its expected SHA-256 must be supplied together"
        )
    if args.retained_source_archive is not None:
        retained = args.retained_source_archive.resolve()
        retained_source_archive_sha256 = sha256_file(retained)
        full_git_archive = run_git(
            repo, "archive", "--format=tar", commit, binary=True
        )
        retained_git_archive_sha256 = sha256_bytes(full_git_archive)
        with retained.open("rb") as handle:
            retained_files = tar_hashes(handle, "r:gz")
        full_git_files = tar_hashes(io.BytesIO(full_git_archive), "r:")
        retained_archive_checks = {
            "retained_archive_sha256": retained_source_archive_sha256
            == args.expected_retained_source_archive_sha256,
            "retained_archive_paths": set(retained_files)
            == set(full_git_files),
            "retained_archive_bytes": retained_files == full_git_files,
        }
        if not all(retained_archive_checks.values()):
            raise SystemExit(
                "retained source archive differs from the exact Git tree: "
                f"{[key for key, value in retained_archive_checks.items() if not value]}"
            )

    source_manifest_path = capsule / "source-files.sha256"
    source_archive_path = capsule / "source.tar.gz"
    build_receipt_path = capsule / "build-receipt.json"
    source_manifest = parse_manifest(source_manifest_path)
    git_files = tar_hashes(io.BytesIO(git_archive), "r:")
    with source_archive_path.open("rb") as handle:
        capsule_files = tar_hashes(handle, "r:gz")
    if source_manifest != git_files:
        raise SystemExit("capsule source manifest differs from the exact Git tree")
    if source_manifest != capsule_files:
        raise SystemExit("capsule source archive differs from its source manifest")

    build_receipt = json.loads(build_receipt_path.read_text(encoding="utf-8"))
    source = build_receipt.get("source") or {}
    source_manifest_sha256 = sha256_file(source_manifest_path)
    source_archive_sha256 = sha256_file(source_archive_path)
    checks = {
        "build_receipt_verified": build_receipt.get("status")
        == "verified_reproducible",
        "build_receipt_source_manifest": source.get("manifest_sha256")
        == source_manifest_sha256,
        "build_receipt_source_archive": source.get("archive_sha256")
        == source_archive_sha256,
        "git_and_manifest_paths": set(git_files) == set(source_manifest),
        "git_and_manifest_bytes": git_files == source_manifest,
        "archive_and_manifest_bytes": capsule_files == source_manifest,
        **retained_archive_checks,
    }
    if not all(checks.values()):
        raise SystemExit(
            "source identity checks failed: "
            f"{[name for name, passed in checks.items() if not passed]}"
        )

    receipt = {
        "schema_version": 1,
        "status": "verified_exact_git_source",
        "repository": repository,
        "commit": commit,
        "tree": tree,
        "commit_timestamp": timestamp,
        "git_archive_command": [
            "/usr/bin/git",
            "archive",
            "--format=tar",
            commit,
            "engine",
            "tests",
        ],
        "git_archive_sha256": git_archive_sha256,
        "retained_source_archive_sha256": retained_source_archive_sha256,
        "retained_git_archive_sha256": retained_git_archive_sha256,
        "source_file_count": len(source_manifest),
        "source_manifest_sha256": source_manifest_sha256,
        "capsule_source_archive_sha256": source_archive_sha256,
        "build_receipt_sha256": sha256_file(build_receipt_path),
        "git_executable": "/usr/bin/git",
        "git_executable_sha256": sha256_file(Path("/usr/bin/git")),
        "git_version": run_git(repo, "--version"),
        "verifier_sha256": sha256_file(Path(__file__)),
        "checks": checks,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        dir=args.output.parent,
        prefix=args.output.name + ".tmp.",
        delete=False,
    ) as handle:
        temporary = Path(handle.name)
        json.dump(receipt, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(temporary, args.output)
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
