#!/usr/bin/env python3
"""Fingerprint a validated common-format taxonomy without materializing pairs."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import resource
import time
from pathlib import Path


def frame(digest: "hashlib._Hash", value: str) -> None:
    encoded = value.encode("utf-8")
    digest.update(len(encoded).to_bytes(8, "big")); digest.update(encoded)


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output-prefix", required=True, type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    rows = args.input.open(encoding="utf-8")
    metadata: dict[str, str] = {}
    consistency = None
    unsat: list[str] = []
    pair_count = 0
    nonempty_lefts = 0
    previous_unsat = None
    previous_pair = None
    current_left = None
    current_count = 0
    current_digest = hashlib.sha256()
    node_path = Path(str(args.output_prefix) + ".nodes.tsv.gz")
    unsat_path = Path(str(args.output_prefix) + ".unsat.txt.gz")
    args.output_prefix.parent.mkdir(parents=True, exist_ok=True)

    def publish_left(handle) -> None:
        nonlocal current_left, current_count, current_digest, nonempty_lefts
        if current_left is None: return
        right_hash = current_digest.hexdigest()
        handle.write(f"{current_left}\t{current_count}\t{right_hash}\n")
        nonempty_lefts += 1
        current_left = None; current_count = 0; current_digest = hashlib.sha256()

    saw_terminal = False
    with gzip.open(node_path, "wt", encoding="utf-8") as node_handle:
        for line_number, raw in enumerate(rows, 1):
            line = raw.rstrip("\n")
            fields = line.split("\t")
            if fields[0] == "M" and len(fields) == 3:
                if fields[1] in metadata: raise ValueError(f"duplicate metadata at {line_number}")
                metadata[fields[1]] = fields[2]
            elif fields[0] == "C" and len(fields) == 2:
                if consistency is not None or fields[1] not in {"true", "false", "unknown"}:
                    raise ValueError("invalid consistency")
                consistency = fields[1]
            elif fields[0] == "U" and len(fields) == 2:
                if previous_unsat is not None and fields[1] <= previous_unsat:
                    raise ValueError("unsatisfiable rows not sorted and unique")
                previous_unsat = fields[1]; unsat.append(fields[1])
            elif fields[0] == "S" and len(fields) == 3:
                pair = (fields[1], fields[2])
                if fields[1] == fields[2] or (previous_pair is not None and pair <= previous_pair):
                    raise ValueError("subsumption rows invalid or not sorted and unique")
                previous_pair = pair
                if current_left != fields[1]: publish_left(node_handle); current_left = fields[1]
                frame(current_digest, fields[2]); current_count += 1; pair_count += 1
            elif line == "Z\tcomplete":
                if saw_terminal: raise ValueError("duplicate terminal sentinel")
                saw_terminal = True
            else:
                raise ValueError(f"invalid row {line_number}")
        publish_left(node_handle)
    rows.close()
    if not saw_terminal or consistency is None or metadata.get("schema") != "1":
        raise ValueError("incomplete output")
    if int(metadata.get("subsumptions", "-1")) != pair_count or int(metadata.get("unsatisfiable", "-1")) != len(unsat):
        raise ValueError("metadata count mismatch")

    # Match the full-IRI fingerprint's ordering: consistency precedes pairs.
    # Pair bytes were accumulated above, so rebuild the final digest from the
    # compact node file without loading the relation.
    final_taxonomy = hashlib.sha256()
    final_taxonomy.update(b"consistent\x01" if consistency == "true" else
                          b"consistent\x00" if consistency == "false" else b"consistent\x02")
    relation_digest = hashlib.sha256()
    with gzip.open(node_path, "rt", encoding="utf-8") as stream:
        for line in stream:
            left, count, right_hash = line.rstrip("\n").split("\t")
            for value in (final_taxonomy, relation_digest):
                value.update(b"P"); frame(value, left)
                value.update(int(count).to_bytes(8, "big")); value.update(bytes.fromhex(right_hash))
    final_taxonomy.update(b"U"); relation_digest.update(b"U")
    with gzip.open(unsat_path, "wt", encoding="utf-8") as stream:
        for iri in unsat:
            stream.write(iri + "\n")
            frame(final_taxonomy, iri); frame(relation_digest, iri)
    record = {
        "schema_version": 1, "algorithm": "full-iri-common-stream-fingerprint-v1",
        "status": "ok", "consistent": consistency, "subsumptions": pair_count,
        "unsatisfiable": len(unsat), "nonempty_lefts": nonempty_lefts,
        "input": str(args.input), "input_sha256": sha256(args.input),
        "taxonomy_sha256": final_taxonomy.hexdigest(),
        "relation_sha256": relation_digest.hexdigest(),
        "node_fingerprints": str(node_path), "node_fingerprints_sha256": sha256(node_path),
        "unsatisfiable_names": str(unsat_path), "unsatisfiable_names_sha256": sha256(unsat_path),
        "wall_s": round(time.monotonic() - started, 4),
        "peak_mb": round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024, 2),
    }
    output = Path(str(args.output_prefix) + ".json"); temporary = Path(str(output) + ".part")
    temporary.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(output); print(json.dumps(record, sort_keys=True))


if __name__ == "__main__":
    main()
