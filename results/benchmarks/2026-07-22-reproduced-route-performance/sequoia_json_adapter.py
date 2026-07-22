#!/usr/bin/env python3
"""Adapt Sequoia's Functional Syntax taxonomy to KM/HermiT JSON."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


SUBCLASS = re.compile(
    r"SubClassOf\(\s*(<[^>]+>|[\w:]+)\s+(<[^>]+>|[\w:]+)\s*\)"
)
EQUIVALENT = re.compile(r"EquivalentClasses\(\s*([^)]+?)\s*\)")
TOKEN = re.compile(r"<[^>]+>|[A-Za-z][\w:.\-]*")


def clean(value: str) -> str:
    value = value.strip()
    if value.startswith("<") and value.endswith(">"):
        return value[1:-1]
    if value == "owl:Thing":
        return "http://www.w3.org/2002/07/owl#Thing"
    if value == "owl:Nothing":
        return "http://www.w3.org/2002/07/owl#Nothing"
    return value


def main() -> int:
    if len(sys.argv) != 3 or sys.argv[1] != "classify":
        print("usage: sequoia_json_adapter.py classify ONTOLOGY", file=sys.stderr)
        return 2
    binary = os.environ.get("SEQUOIA_BINARY")
    if not binary or not Path(binary).is_file():
        print("SEQUOIA_BINARY does not name a file", file=sys.stderr)
        return 2
    mode = os.environ.get("SEQUOIA_MODE", "strict")
    options = {
        "strict": [],
        "ignore_unsupported": ["--ignoreUnsupportedFeatures"],
    }.get(mode)
    if options is None:
        print(f"unknown SEQUOIA_MODE={mode!r}", file=sys.stderr)
        return 2

    with tempfile.TemporaryDirectory(prefix="sequoia-classification-") as directory:
        taxonomy = Path(directory) / "taxonomy.ofn"
        log = Path(directory) / "sequoia.log"
        child_environment = dict(os.environ)
        child_environment["JAVA_OPTS"] = "-Xms256m -Xmx16g -XX:+UseG1GC"
        with log.open("wb") as log_handle:
            completed = subprocess.run(
                [
                    binary,
                    "-main",
                    "com.sequoiareasoner.cli.Sequoia",
                    "classify",
                    *options,
                    "--output",
                    str(taxonomy),
                    sys.argv[2],
                ],
                stdin=subprocess.DEVNULL,
                stdout=log_handle,
                stderr=subprocess.STDOUT,
                env=child_environment,
                check=False,
            )
        log_text = log.read_text(encoding="utf-8", errors="replace")
        sys.stderr.write(log_text)
        if completed.returncode != 0:
            lowered = log_text.lower()
            if "ontology is inconsistent" in lowered:
                print('{"consistent":false,"subsumptions":[],"unsatisfiable":[]}')
                return 0
            if "unsupported" in lowered or "not supported" in lowered:
                return 3
            return completed.returncode
        if not taxonomy.is_file():
            print("Sequoia returned success without a taxonomy file", file=sys.stderr)
            return 2

        text = taxonomy.read_text(encoding="utf-8", errors="replace")
        subsumptions = [
            [clean(match.group(1)), clean(match.group(2))]
            for match in SUBCLASS.finditer(text)
        ]
        for match in EQUIVALENT.finditer(text):
            names = [clean(token) for token in TOKEN.findall(match.group(1))]
            if len(names) < 2:
                continue
            representative = names[0]
            for other in names[1:]:
                subsumptions.append([representative, other])
                subsumptions.append([other, representative])
        json.dump(
            {
                "consistent": True,
                "subsumptions": subsumptions,
                "unsatisfiable": [],
            },
            sys.stdout,
            separators=(",", ":"),
            sort_keys=True,
        )
        sys.stdout.write("\n")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
