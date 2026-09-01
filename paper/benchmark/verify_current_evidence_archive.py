#!/usr/bin/env python3
"""Stream-verify the packaged contemporary OBO benchmark evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tarfile

from import_current_final import BASELINES, FINAL_FILES, digest_manifest


RESULT = re.compile(r"current-results/([^/]+)/([^/]+)\.result\.json")
FORBIDDEN = re.compile(
    r"(^|/)(merged|sources|runtimes)(/|$)|\.taxonomy\.|\.jar$|"
    r"\.(exe|dll|dylib|so)$|(^|/)(km|konclude)$|"
    r"(^|/)Konclude-build|(^|/)(credentials?|secrets?)(/|$)|"
    r"prompt|response|conversation|session-body",
    re.IGNORECASE,
)


def sha_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def sidecar(path: Path, archive: Path) -> str:
    fields = path.read_text(encoding="utf-8").strip().split()
    if len(fields) != 2 or not re.fullmatch(r"[0-9a-f]{64}", fields[0]):
        raise ValueError("malformed evidence-archive digest sidecar")
    if Path(fields[1]).name != archive.name:
        raise ValueError("evidence-archive sidecar names another file")
    if sha_file(archive) != fields[0]:
        raise ValueError("evidence-archive compressed digest mismatch")
    return fields[0]


def verify(archive: Path, digest_sidecar: Path, final: Path) -> dict:
    archive_sha256 = sidecar(digest_sidecar, archive)
    record_manifest = digest_manifest(final / "result-records.sha256")
    expected_final = digest_manifest(final / "SHA256SUMS")
    seen: set[str] = set()
    seen_records: dict[str, str] = {}
    seen_final: dict[str, str] = {}
    readme = False
    members = 0
    with tarfile.open(archive, mode="r:gz") as package:
        for member in package:
            name = member.name.removeprefix("./")
            path = PurePosixPath(name)
            if path.is_absolute() or ".." in path.parts:
                raise ValueError(f"unsafe evidence member path: {name}")
            if name in seen:
                raise ValueError(f"duplicate evidence member path: {name}")
            seen.add(name)
            if not member.isfile():
                raise ValueError(f"non-regular evidence member: {name}")
            if FORBIDDEN.search(name):
                raise ValueError(f"forbidden evidence payload: {name}")
            stream = package.extractfile(member)
            if stream is None:
                raise ValueError(f"cannot read evidence member: {name}")
            digest = hashlib.sha256()
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
            value = digest.hexdigest()
            members += 1
            match = RESULT.fullmatch(name)
            if match:
                if match.group(1) not in BASELINES:
                    raise ValueError(f"unknown result baseline in archive: {name}")
                seen_records[name] = value
            if name.startswith("final/") and name.count("/") == 1:
                seen_final[name.removeprefix("final/")] = value
            if name == "archive/staging/README.md":
                readme = True
    if not readme:
        raise ValueError("evidence archive omits its top-level README")
    if seen_records != record_manifest:
        missing = sorted(set(record_manifest) - set(seen_records))[:3]
        extra = sorted(set(seen_records) - set(record_manifest))[:3]
        wrong = sorted(name for name in set(record_manifest) & set(seen_records)
                       if record_manifest[name] != seen_records[name])[:3]
        raise ValueError(f"result records differ from final manifest: missing={missing}, "
                         f"extra={extra}, wrong_digest={wrong}")
    for name in (*FINAL_FILES, "SHA256SUMS"):
        if name not in seen_final:
            raise ValueError(f"evidence archive omits final/{name}")
        expected = sha_file(final / name)
        if seen_final[name] != expected:
            raise ValueError(f"archived final file differs: {name}")
    if set(expected_final) != set(FINAL_FILES):
        raise ValueError("local final SHA256SUMS has unexpected entries")
    return {
        "schema": 1,
        "status": "verified",
        "archive_sha256": archive_sha256,
        "members": members,
        "result_records": len(seen_records),
        "final_aggregate_sha256": expected_final["current-aggregate.json"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", required=True, type=Path)
    parser.add_argument("--sha256", required=True, type=Path)
    parser.add_argument("--final", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    report = verify(args.archive, args.sha256, args.final)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(f"CURRENT_EVIDENCE_ARCHIVE_OK\t{report['result_records']}\t{report['members']}")


if __name__ == "__main__":
    main()
