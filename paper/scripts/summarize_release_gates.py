#!/usr/bin/env python3
"""Produce a small, hash-bound summary of the exact v1.3 certification logs."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


GATES = {
    "elc": "ELC certification gate passed",
    "ht": "test result: ok. 16 passed; 0 failed",
    "cb": "CB certification gate passed",
    "routing": "routing certification gate passed",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--logs", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    summary = {"schema": 1, "release": "v1.3.0", "commit": "f4738bcdd980a1b2fcc840e4b455d37d447510cb",
               "gates": {}}
    for gate, terminal in GATES.items():
        path = args.logs / f"v1.3-f4738bc-{gate}-cert.log"
        data = path.read_bytes(); text = data.decode(errors="replace")
        problems = []
        if terminal not in text: problems.append("terminal marker")
        if "sorryAx" in text: problems.append("sorryAx")
        if "test result: FAILED" in text or "error: could not compile" in text:
            problems.append("failed build or test")
        blocks = re.findall(r"depends on axioms:\s*\[(.*?)\]", text, re.S)
        axioms = set()
        for block in blocks: axioms.update(re.findall(r"[A-Za-z][A-Za-z0-9_.]*", block))
        if not blocks: problems.append("missing axiom audit")
        if axioms - ALLOWED_AXIOMS: problems.append(f"unexpected axioms {sorted(axioms - ALLOWED_AXIOMS)}")
        if problems: raise ValueError(f"invalid {gate} gate log: {problems}")
        summary["gates"][gate] = {
            "log_sha256": hashlib.sha256(data).hexdigest(),
            "bytes": len(data),
            "axiom_reports": len(blocks),
            "reported_axioms": sorted(axioms),
            "sorryAx": False,
            "terminal_evidence": terminal,
        }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(args.output) + ".part")
    temporary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(args.output)
    print("RELEASE_GATES_OK\t4")


if __name__ == "__main__":
    main()
