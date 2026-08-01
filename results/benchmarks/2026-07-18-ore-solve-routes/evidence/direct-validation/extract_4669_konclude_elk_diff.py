#!/usr/bin/env python3
"""Emit the exact named-pair difference between two projected taxonomies."""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import sys


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--projected", type=Path, required=True)
    parser.add_argument("--konclude", type=Path, required=True)
    parser.add_argument("--elk", type=Path, required=True)
    parser.add_argument("--validator", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location("km_4669_validator", args.validator)
    if spec is None or spec.loader is None:
        raise SystemExit("failed to load validator module")
    validator = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = validator
    spec.loader.exec_module(validator)
    declared = validator.parse_declarations(args.projected)
    konclude = validator.canonical_taxonomy(args.konclude, "owlxml", declared)
    elk = validator.canonical_taxonomy(args.elk, "functional", declared)
    missing = sorted(konclude.pairs - elk.pairs)
    if len(missing) != 54 or elk.pairs - konclude.pairs:
        raise SystemExit("unexpected Konclude/ELK projected-taxonomy difference")
    args.output.write_text(
        "sub_iri\tsuper_iri\n"
        + "".join(f"{left}\t{right}\n" for left, right in missing),
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
