#!/usr/bin/env python3
"""Compare two sorted full-IRI taxonomy TSV files without materialising them.

The Java benchmark writer emits one ``S<TAB>sub<TAB>sup`` row per published
subsumption in lexicographic order.  This comparator fails if either stream is
unsorted or duplicated, then performs a merge difference and records bounded
representative witnesses in both directions.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Dict, Iterator, List, Optional, TextIO, Tuple


Pair = Tuple[str, str]


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def pairs(stream: TextIO, source: Path) -> Iterator[Pair]:
    previous: Optional[Pair] = None
    for number, raw in enumerate(stream, 1):
        if not raw.startswith("S\t"):
            continue
        fields = raw.rstrip("\n").split("\t")
        if len(fields) != 3 or not fields[1] or not fields[2]:
            raise ValueError(f"malformed subsumption at {source}:{number}")
        pair = (fields[1], fields[2])
        if previous is not None and pair <= previous:
            relation = "duplicate" if pair == previous else "unsorted"
            raise ValueError(f"{relation} subsumption at {source}:{number}")
        previous = pair
        yield pair


def advance(iterator: Iterator[Pair]) -> Optional[Pair]:
    return next(iterator, None)


def compare(left_path: Path, right_path: Path, sample_limit: int) -> Dict[str, object]:
    with left_path.open(encoding="utf-8") as left_stream, right_path.open(encoding="utf-8") as right_stream:
        left_iter = pairs(left_stream, left_path)
        right_iter = pairs(right_stream, right_path)
        left = advance(left_iter)
        right = advance(right_iter)
        common = left_only = right_only = 0
        left_sample: List[List[str]] = []
        right_sample: List[List[str]] = []
        while left is not None or right is not None:
            if right is None or (left is not None and left < right):
                left_only += 1
                if len(left_sample) < sample_limit:
                    left_sample.append(list(left))
                left = advance(left_iter)
            elif left is None or right < left:
                right_only += 1
                if len(right_sample) < sample_limit:
                    right_sample.append(list(right))
                right = advance(right_iter)
            else:
                common += 1
                left = advance(left_iter)
                right = advance(right_iter)
    return {
        "schema": 1,
        "left": str(left_path),
        "left_sha256": digest(left_path),
        "right": str(right_path),
        "right_sha256": digest(right_path),
        "common": common,
        "left_only": left_only,
        "right_only": right_only,
        "left_total": common + left_only,
        "right_total": common + right_only,
        "left_only_sample": left_sample,
        "right_only_sample": right_sample,
        "relation": (
            "equal" if left_only == right_only == 0 else
            "left_strict_subset" if left_only == 0 else
            "right_strict_subset" if right_only == 0 else
            "incomparable"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--left", required=True, type=Path)
    parser.add_argument("--right", required=True, type=Path)
    parser.add_argument("--left-label", default="left")
    parser.add_argument("--right-label", default="right")
    parser.add_argument("--sample-limit", type=int, default=20)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.sample_limit < 0:
        raise SystemExit("sample limit must be nonnegative")
    payload = compare(args.left, args.right, args.sample_limit)
    payload["left_label"] = args.left_label
    payload["right_label"] = args.right_label
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        "TAXONOMY_DIFF_OK",
        args.left_label,
        args.right_label,
        payload["relation"],
        payload["left_only"],
        payload["right_only"],
        sep="\t",
    )


if __name__ == "__main__":
    main()
