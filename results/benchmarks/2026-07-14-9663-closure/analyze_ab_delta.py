#!/usr/bin/env python3
"""Report the exact classification delta between two KM JSON outputs."""

import argparse
import collections
import gzip
import json
from pathlib import Path


def local_name(iri: str) -> str:
    iri = iri.rstrip("/")
    iri = iri.split("#")[-1].split("/")[-1]
    return iri.split("__", 1)[0] if "__" in iri else iri


def load_km(path: Path):
    with path.open() as stream:
        document = json.load(stream)
    pairs = {
        (local_name(sub), local_name(sup))
        for sub, sup in document.get("subsumptions", [])
        if local_name(sub) != local_name(sup)
        and local_name(sup) not in {"Thing", "owlThing", "owlNothing"}
    }
    return document, pairs


def load_gold(path: Path):
    pairs = set()
    with gzip.open(path, "rt") as stream:
        for line_number, line in enumerate(stream):
            fields = line.split()
            if line_number > 0 and len(fields) == 2:
                sub, sup = map(local_name, fields)
                if sub != sup and sup not in {"Thing", "owlThing", "owlNothing"}:
                    pairs.add((sub, sup))
    return pairs


def prefix(name: str) -> str:
    return name.split("_", 1)[0]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    parser.add_argument("gold", type=Path)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()

    before_document, before = load_km(args.before)
    after_document, after = load_km(args.after)
    gold = load_gold(args.gold)
    lost = before - after
    gained = after - before
    newly_missing = (gold - after) - (gold - before)
    newly_recovered = (gold - before) - (gold - after)
    newly_extra = (after - gold) - (before - gold)
    removed_extra = (before - gold) - (after - gold)

    summary = {
        "before_consistent": before_document.get("consistent"),
        "after_consistent": after_document.get("consistent"),
        "before_pairs": len(before),
        "after_pairs": len(after),
        "gold_pairs": len(gold),
        "before_missing": len(gold - before),
        "after_missing": len(gold - after),
        "before_extra": len(before - gold),
        "after_extra": len(after - gold),
        "lost_pairs": len(lost),
        "gained_pairs": len(gained),
        "newly_missing": len(newly_missing),
        "newly_recovered": len(newly_recovered),
        "newly_extra": len(newly_extra),
        "removed_extra": len(removed_extra),
        "newly_missing_subjects": len({sub for sub, _ in newly_missing}),
        "newly_missing_superclasses": len({sup for _, sup in newly_missing}),
        "newly_missing_subject_prefixes": collections.Counter(
            prefix(sub) for sub, _ in newly_missing
        ).most_common(),
        "newly_missing_superclass_prefixes": collections.Counter(
            prefix(sup) for _, sup in newly_missing
        ).most_common(),
        "top_newly_missing_superclasses": collections.Counter(
            sup for _, sup in newly_missing
        ).most_common(100),
        "first_newly_missing": [list(pair) for pair in sorted(newly_missing)[:200]],
        "first_newly_recovered": [list(pair) for pair in sorted(newly_recovered)[:200]],
        "first_newly_extra": [list(pair) for pair in sorted(newly_extra)[:200]],
        "first_removed_extra": [list(pair) for pair in sorted(removed_extra)[:200]],
    }

    args.output_dir.mkdir(parents=True, exist_ok=True)
    with (args.output_dir / "ab-delta-summary.json").open("w") as stream:
        json.dump(summary, stream, indent=2, sort_keys=True)
        stream.write("\n")
    for name, pairs in (
        ("lost", lost),
        ("gained", gained),
        ("newly-missing", newly_missing),
        ("newly-recovered", newly_recovered),
        ("newly-extra", newly_extra),
        ("removed-extra", removed_extra),
    ):
        with gzip.open(args.output_dir / f"{name}.tsv.gz", "wt") as stream:
            for sub, sup in sorted(pairs):
                stream.write(f"{sub}\t{sup}\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
