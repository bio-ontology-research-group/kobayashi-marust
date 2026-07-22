#!/usr/bin/env python3
"""Adapt rustdl's direct-edge text classification to KM/HermiT JSON."""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def main() -> int:
    if len(sys.argv) != 3 or sys.argv[1] != "classify":
        print("usage: rustdl_json_adapter.py classify ONTOLOGY", file=sys.stderr)
        return 2
    binary = os.environ.get("RUSTDL_BINARY")
    if not binary or not Path(binary).is_file():
        print("RUSTDL_BINARY does not name a file", file=sys.stderr)
        return 2
    mode = os.environ.get("RUSTDL_MODE", "complete")
    options = {
        "complete": ["--pair-timeout-ms", "0", "--global-timeout-ms", "0"],
        "default": [],
    }.get(mode)
    if options is None:
        print(f"unknown RUSTDL_MODE={mode!r}", file=sys.stderr)
        return 2

    temporary = tempfile.NamedTemporaryFile(
        prefix="rustdl-classification-", suffix=".txt", delete=False
    )
    temporary_path = Path(temporary.name)
    try:
        with temporary:
            completed = subprocess.run(
                [binary, "classify", sys.argv[2], *options],
                stdin=subprocess.DEVNULL,
                stdout=temporary,
                stderr=sys.stderr,
                check=False,
            )
        if completed.returncode != 0:
            return completed.returncode

        consistent = True
        subsumptions: list[list[str]] = []
        unsatisfiable: list[str] = []
        with temporary_path.open(encoding="utf-8", errors="replace") as handle:
            for raw_line in handle:
                line = raw_line.rstrip("\n")
                if line == "# abox_check: inconsistent":
                    consistent = False
                    continue
                fields = line.split("\t")
                if len(fields) == 3 and fields[0] == "direct":
                    subsumptions.append([fields[1], fields[2]])
                elif len(fields) >= 3 and fields[0] == "equiv":
                    representative = fields[1]
                    for other in fields[2:]:
                        subsumptions.append([representative, other])
                        subsumptions.append([other, representative])
                elif len(fields) == 2 and fields[0] == "unsat":
                    unsatisfiable.append(fields[1])
        json.dump(
            {
                "consistent": consistent,
                "subsumptions": subsumptions,
                "unsatisfiable": unsatisfiable,
            },
            sys.stdout,
            separators=(",", ":"),
            sort_keys=True,
        )
        sys.stdout.write("\n")
        return 0
    finally:
        try:
            temporary_path.unlink()
        except OSError:
            pass


if __name__ == "__main__":
    raise SystemExit(main())
