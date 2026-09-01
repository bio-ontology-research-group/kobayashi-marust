#!/usr/bin/env python3
"""Fingerprint KM's complete sorted JSON taxonomy with bounded memory.

KM publishes the complete named-class relation, already sorted by full IRI.
The generic external-reasoner fingerprinter must reconstruct transitive closure,
but doing that again for KM first materializes multi-gigabyte JSON and can exceed
the benchmark allocation.  This parser validates and hashes KM's publication
contract directly while retaining the same digest framing.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import resource
import time
from typing import Callable


TOP = "http://www.w3.org/2002/07/owl#Thing"
BOTTOM = "http://www.w3.org/2002/07/owl#Nothing"
DECL_FUN = re.compile(r"Declaration\(\s*Class\(\s*(<[^>]+>|[\w:]+)\s*\)\s*\)")


def clean_iri(value: str) -> str:
    value = value.strip()
    if value.startswith("<") and value.endswith(">"):
        value = value[1:-1]
    if value in ("owl:Thing", "Thing", "thing"):
        return TOP
    if value in ("owl:Nothing", "Nothing", "nothing"):
        return BOTTOM
    return value


def frame(digest, value: str) -> None:
    encoded = value.encode("utf-8")
    digest.update(len(encoded).to_bytes(8, "big"))
    digest.update(encoded)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def source_declarations(path: Path | None) -> set[str]:
    if path is None:
        return set()
    declared: set[str] = set()
    with path.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            declared.update(clean_iri(match.group(1)) for match in DECL_FUN.finditer(line))
    return declared


class JsonStream:
    """Small incremental JSON reader sufficient for one flat result object."""

    def __init__(self, path: Path, chunk_size: int = 1024 * 1024) -> None:
        self.handle = path.open(encoding="utf-8")
        self.chunk_size = chunk_size
        self.buffer = ""
        self.position = 0
        self.eof = False
        self.decoder = json.JSONDecoder()

    def close(self) -> None:
        self.handle.close()

    def compact(self) -> None:
        if self.position:
            self.buffer = self.buffer[self.position:]
            self.position = 0

    def fill(self) -> bool:
        self.compact()
        chunk = self.handle.read(self.chunk_size)
        if not chunk:
            self.eof = True
            return False
        self.buffer += chunk
        return True

    def skip_space(self) -> None:
        while True:
            while self.position < len(self.buffer) and self.buffer[self.position].isspace():
                self.position += 1
            if self.position < len(self.buffer) or not self.fill():
                return

    def peek(self) -> str:
        self.skip_space()
        if self.position >= len(self.buffer):
            raise ValueError("unexpected end of JSON")
        return self.buffer[self.position]

    def expect(self, token: str) -> None:
        if self.peek() != token:
            raise ValueError(f"expected {token!r} in JSON")
        self.position += 1

    def value(self):
        self.skip_space()
        while True:
            try:
                value, end = self.decoder.raw_decode(self.buffer, self.position)
                self.position = end
                return value
            except json.JSONDecodeError as error:
                remaining = len(self.buffer) - self.position
                if self.eof or remaining > 16 * 1024 * 1024 or not self.fill():
                    raise ValueError(f"invalid or oversized JSON value: {error}") from error

    def array(self, visit: Callable[[object], None]) -> None:
        self.expect("[")
        if self.peek() == "]":
            self.position += 1
            return
        while True:
            visit(self.value())
            separator = self.peek()
            self.position += 1
            if separator == "]":
                return
            if separator != ",":
                raise ValueError("expected comma or array terminator")


def scan(path: Path, visit_pair: Callable[[str, str], None],
         visit_unsat: Callable[[str], None]) -> bool:
    stream = JsonStream(path)
    consistent = None
    seen: set[str] = set()
    try:
        stream.expect("{")
        if stream.peek() == "}":
            raise ValueError("empty KM result object")
        while True:
            key = stream.value()
            if not isinstance(key, str) or key in seen:
                raise ValueError("invalid or duplicate KM result key")
            seen.add(key)
            stream.expect(":")
            if key == "subsumptions":
                def pair(value: object) -> None:
                    if (not isinstance(value, list) or len(value) != 2
                            or not all(isinstance(item, str) for item in value)):
                        raise ValueError("invalid KM subsumption pair")
                    visit_pair(clean_iri(value[0]), clean_iri(value[1]))
                stream.array(pair)
            elif key == "unsatisfiable":
                def unsat(value: object) -> None:
                    if not isinstance(value, str):
                        raise ValueError("invalid KM unsatisfiable class")
                    visit_unsat(clean_iri(value))
                stream.array(unsat)
            else:
                value = stream.value()
                if key == "consistent":
                    if not isinstance(value, bool):
                        raise ValueError("invalid KM consistency value")
                    consistent = value
            separator = stream.peek()
            stream.position += 1
            if separator == "}":
                break
            if separator != ",":
                raise ValueError("expected comma or object terminator")
        stream.skip_space()
        if stream.position != len(stream.buffer) or not stream.eof and stream.fill():
            stream.skip_space()
            if stream.position != len(stream.buffer):
                raise ValueError("trailing content after KM result")
    finally:
        stream.close()
    if consistent is None or not {"subsumptions", "unsatisfiable"}.issubset(seen):
        raise ValueError("incomplete KM result object")
    return consistent


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--source-ontology", type=Path)
    parser.add_argument("--output-prefix", required=True, type=Path)
    args = parser.parse_args()
    started = time.monotonic()

    explicit_unsat: set[str] = set()
    bottom_reachable: set[str] = set()
    source_edges = 0
    previous_pair: tuple[str, str] | None = None

    def inspect_pair(left: str, right: str) -> None:
        nonlocal source_edges, previous_pair
        pair = (left, right)
        if previous_pair is not None and pair <= previous_pair:
            raise ValueError("KM subsumptions are not sorted and unique")
        previous_pair = pair
        source_edges += 1
        if right == BOTTOM:
            bottom_reachable.add(left)

    def inspect_unsat(value: str) -> None:
        if value in explicit_unsat:
            raise ValueError("duplicate KM unsatisfiable class")
        explicit_unsat.add(value)

    consistent = scan(args.input, inspect_pair, inspect_unsat)
    unsat = explicit_unsat | bottom_reachable
    if TOP in unsat:
        consistent = False
    if not consistent:
        unsat.clear()

    taxonomy_digest = hashlib.sha256()
    taxonomy_digest.update(b"consistent\x01" if consistent else b"consistent\x00")
    relation_digest = hashlib.sha256()
    node_path = Path(str(args.output_prefix) + ".nodes.tsv.gz")
    unsat_path = Path(str(args.output_prefix) + ".unsat.txt.gz")
    args.output_prefix.parent.mkdir(parents=True, exist_ok=True)
    pair_count = 0
    nonempty_lefts = 0
    current_left: str | None = None
    current_count = 0
    current_digest = hashlib.sha256()

    def publish(handle) -> None:
        nonlocal current_left, current_count, current_digest, pair_count, nonempty_lefts
        if current_left is None:
            return
        right_hash = current_digest.hexdigest()
        handle.write(f"{current_left}\t{current_count}\t{right_hash}\n")
        for digest in (taxonomy_digest, relation_digest):
            digest.update(b"P")
            frame(digest, current_left)
            digest.update(current_count.to_bytes(8, "big"))
            digest.update(bytes.fromhex(right_hash))
        pair_count += current_count
        nonempty_lefts += 1
        current_left = None
        current_count = 0
        current_digest = hashlib.sha256()

    previous_filtered: tuple[str, str] | None = None
    with gzip.open(node_path, "wt", encoding="utf-8") as node_handle:
        if consistent:
            def hash_pair(left: str, right: str) -> None:
                nonlocal current_left, current_count, previous_filtered
                if (left == right or left in {TOP, BOTTOM} or right in {TOP, BOTTOM}
                        or left in unsat or right in unsat):
                    return
                pair = (left, right)
                if previous_filtered is not None and pair <= previous_filtered:
                    raise ValueError("filtered KM relation is not sorted and unique")
                previous_filtered = pair
                if current_left != left:
                    publish(node_handle)
                    current_left = left
                frame(current_digest, right)
                current_count += 1
            scan(args.input, hash_pair, lambda _value: None)
            publish(node_handle)

    taxonomy_digest.update(b"U")
    relation_digest.update(b"U")
    with gzip.open(unsat_path, "wt", encoding="utf-8") as handle:
        for name in sorted(unsat):
            handle.write(name + "\n")
            frame(taxonomy_digest, name)
            frame(relation_digest, name)

    declarations = source_declarations(args.source_ontology)
    record = {
        "schema_version": 1,
        "algorithm": "km-complete-json-stream-fingerprint-v1",
        "status": "ok",
        "consistent": bool(consistent),
        "subsumptions": pair_count,
        "unsatisfiable": len(unsat),
        "nonempty_lefts": nonempty_lefts,
        "components": None,
        "source_edges": source_edges,
        "source_equivalence_groups": 0,
        "source_declarations": 0,
        "output_declarations": 0,
        "ontology_declarations": len(declarations),
        "missing_source_declarations": len(declarations),
        "source_ontology": str(args.source_ontology) if args.source_ontology else None,
        "source_ontology_sha256": sha256_file(args.source_ontology) if args.source_ontology else None,
        "input": str(args.input),
        "input_sha256": sha256_file(args.input),
        "format": "json",
        "taxonomy_sha256": taxonomy_digest.hexdigest(),
        "relation_sha256": relation_digest.hexdigest(),
        "node_fingerprints": str(node_path),
        "node_fingerprints_sha256": sha256_file(node_path),
        "unsatisfiable_names": str(unsat_path),
        "unsatisfiable_names_sha256": sha256_file(unsat_path),
        "wall_s": round(time.monotonic() - started, 4),
        "peak_mb": round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024, 2),
    }
    output = Path(str(args.output_prefix) + ".json")
    temporary = Path(str(output) + ".part")
    temporary.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(output)
    print(json.dumps(record, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
