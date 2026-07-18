#!/usr/bin/env python3
"""Canonicalize one retained validation output and persist its exact signature."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import time


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_module(path: Path):
    spec = importlib.util.spec_from_file_location("ore_canon_validation", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load canonicalizer: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def signature_lines(consistent: bool, pairs, unsat):
    yield "1\n" if consistent else "0\n"
    for left, right in sorted(pairs):
        yield f"{left}\t{right}\n"
    yield "#UNSAT\n"
    for concept in sorted(unsat):
        yield f"{concept}\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--canonicalizer", type=Path, required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--format", choices=("json", "functional", "owlxml"), required=True)
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    started = time.monotonic()
    module = load_module(args.canonicalizer)
    text = args.input.read_text(encoding="utf-8", errors="replace")
    consistent, pairs, unsat, capped = module.canonicalize(text, args.format)
    record = {
        "schema_version": 1,
        "status": "capped" if capped else "ok",
        "consistent": bool(consistent),
        "subsumptions": len(pairs),
        "unsatisfiable": len(unsat),
        "capped": bool(capped),
        "input": str(args.input),
        "input_sha256": sha256_file(args.input),
        "canonicalizer": str(args.canonicalizer),
        "canonicalizer_sha256": sha256_file(args.canonicalizer),
        "format": args.format,
    }
    if not capped:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        digest = hashlib.sha256()
        with gzip.open(args.output, "wt", encoding="utf-8") as handle:
            for line in signature_lines(consistent, pairs, unsat):
                digest.update(line.encode("utf-8"))
                handle.write(line)
        record.update(
            signature=str(args.output),
            signature_sha256=digest.hexdigest(),
            signature_gzip_sha256=sha256_file(args.output),
            signature_bytes=args.output.stat().st_size,
        )
    record["wall_s"] = round(time.monotonic() - started, 4)
    result_path = args.output.with_suffix(args.output.suffix + ".json")
    result_tmp = result_path.with_suffix(result_path.suffix + ".tmp")
    result_tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    result_tmp.replace(result_path)
    print(json.dumps(record, sort_keys=True), flush=True)
    return 0 if not capped else 3


if __name__ == "__main__":
    raise SystemExit(main())
