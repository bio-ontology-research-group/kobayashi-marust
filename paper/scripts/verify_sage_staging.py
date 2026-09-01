#!/usr/bin/env python3
"""Verify a built Sage staging tree and emit a source-bound receipt."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


FORBIDDEN_LOG = re.compile(
    r"undefined|Overfull|multiply defined|LaTeX Error|Package .* Error",
    re.IGNORECASE,
)


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=Path("paper/main.tex"))
    parser.add_argument("--staging-dir", type=Path, required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("paper/generated/sage-staging-verification.json"),
    )
    args = parser.parse_args()

    source = args.source.resolve()
    staging = args.staging_dir.resolve()
    names = ("main-swj.tex", "main-swj.pdf", "main-swj.log", "sagej.cls", "SageH.bst")
    files = {name: staging / name for name in names}
    missing = [str(path) for path in files.values() if not path.is_file()]
    if missing:
        raise SystemExit("missing Sage build files: " + ", ".join(missing))

    staged_text = files["main-swj.tex"].read_text(encoding="utf-8")
    class_match = re.search(r"\\documentclass\[([^]]*)\]\{sagej\}", staged_text)
    if not class_match:
        raise SystemExit("staged manuscript does not use sagej")
    class_options = class_match.group(1)
    log = files["main-swj.log"].read_text(encoding="utf-8", errors="replace")
    forbidden = sorted(set(match.group(0) for match in FORBIDDEN_LOG.finditer(log)))
    if forbidden:
        raise SystemExit("Sage build log contains forbidden diagnostics: " + ", ".join(forbidden))

    info = subprocess.run(
        ["pdfinfo", str(files["main-swj.pdf"])],
        check=True,
        text=True,
        capture_output=True,
    ).stdout
    page_match = re.search(r"^Pages:\s+(\d+)$", info, re.MULTILINE)
    if not page_match:
        raise SystemExit("could not read Sage PDF page count")

    payload = {
        "schema": 1,
        "status": "pass",
        "source": str(source),
        "source_sha256": digest(source),
        "class": "sagej 2017/01/17 v1.20",
        "class_options": class_options,
        "pages": int(page_match.group(1)),
        "files": {name: digest(path) for name, path in sorted(files.items())},
        "log_policy": FORBIDDEN_LOG.pattern,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"SAGE_STAGING_VERIFIED\t{payload['pages']}\t{payload['source_sha256']}")


if __name__ == "__main__":
    main()
