#!/usr/bin/env python3

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
    with path.open() as handle:
        document = json.load(handle)
    pairs = {
        (local_name(sub), local_name(sup))
        for sub, sup in document.get("subsumptions", [])
        if local_name(sub) != local_name(sup)
        and local_name(sup) not in {"Thing", "owlThing", "owlNothing"}
    }
    return document, pairs


def load_gold(path: Path):
    pairs = set()
    consistent = None
    with gzip.open(path, "rt") as handle:
        for line_number, line in enumerate(handle):
            fields = line.split()
            if line_number == 0 and len(fields) == 1:
                consistent = fields[0]
            elif len(fields) == 2:
                sub, sup = map(local_name, fields)
                if sub != sup and sup not in {"Thing", "owlThing", "owlNothing"}:
                    pairs.add((sub, sup))
    return consistent, pairs


def rows(pairs):
    result = collections.defaultdict(set)
    for sub, sup in pairs:
        result[sub].add(sup)
    return result


def quantiles(values):
    values = sorted(values)
    if not values:
        return {}
    return {
        str(percentile): values[round((len(values) - 1) * percentile / 100)]
        for percentile in (0, 25, 50, 75, 90, 95, 99, 100)
    }


def prefix(name):
    return name.split("_", 1)[0]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("km_json", type=Path)
    parser.add_argument("gold_signature", type=Path)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()

    args.output_dir.mkdir(parents=True, exist_ok=True)
    km_document, km = load_km(args.km_json)
    gold_consistent, gold = load_gold(args.gold_signature)
    missing = gold - km
    extra = km - gold
    km_rows = rows(km)
    gold_rows = rows(gold)

    missing_by_sub = rows(missing)
    missing_by_sup = collections.Counter(sup for _, sup in missing)
    two_hop_witnesses = {}
    gold_tail_witnesses = {}
    all_gold_tail_witnesses = collections.Counter()
    for sub, sup in sorted(missing):
        witness = next(
            (mid for mid in km_rows[sub] if sup in km_rows.get(mid, ())),
            None,
        )
        if witness is not None:
            two_hop_witnesses[(sub, sup)] = witness
        candidates = sorted(mid for mid in km_rows[sub] if sup in gold_rows.get(mid, ()))
        gold_witness = candidates[0] if candidates else None
        if gold_witness is not None:
            gold_tail_witnesses[(sub, sup)] = gold_witness
        for mid in candidates:
            all_gold_tail_witnesses[(sup, mid)] += 1

    subject_rows = []
    for sub, missing_supers in missing_by_sub.items():
        subject_rows.append(
            {
                "subject": sub,
                "missing": len(missing_supers),
                "km": len(km_rows[sub]),
                "gold": len(gold_rows[sub]),
                "missing_supers": sorted(missing_supers),
            }
        )
    subject_rows.sort(key=lambda row: (-row["missing"], row["subject"]))
    missing_subject_set = set(missing_by_sub)
    missing_frontier = sorted(
        sub
        for sub in missing_subject_set
        if not (km_rows[sub] & missing_subject_set)
    )

    focus = [
        "AEO_0000179",
        "AEO_0000195",
        "UBERON_0010229",
        "UBERON_0000057",
        "UBERON_0000061",
        "UBERON_0000465",
        "UBERON_0000477",
        "UBERON_0000480",
        "UBERON_0001062",
        "BFO_0000040",
        "BFO_0000004",
        "BFO_0000002",
        "BFO_0000001",
    ]
    summary = {
        "km_consistent": km_document.get("consistent"),
        "gold_consistent_marker": gold_consistent,
        "km_pairs": len(km),
        "gold_pairs": len(gold),
        "missing_pairs": len(missing),
        "extra_pairs": len(extra),
        "missing_subjects": len(missing_by_sub),
        "missing_superclasses": len(missing_by_sup),
        "missing_frontier_subjects": len(missing_frontier),
        "missing_per_subject_quantiles": quantiles(
            [len(values) for values in missing_by_sub.values()]
        ),
        "km_row_sizes_for_missing_subjects": quantiles(
            [len(km_rows[sub]) for sub in missing_by_sub]
        ),
        "gold_row_sizes_for_missing_subjects": quantiles(
            [len(gold_rows[sub]) for sub in missing_by_sub]
        ),
        "missing_with_exact_km_two_hop_witness": len(two_hop_witnesses),
        "missing_with_km_first_leg_and_gold_tail": len(gold_tail_witnesses),
        "missing_with_gold_reverse": sum((sup, sub) in gold for sub, sup in missing),
        "missing_with_km_reverse": sum((sup, sub) in km for sub, sup in missing),
        "missing_subject_prefixes": collections.Counter(
            prefix(sub) for sub in missing_by_sub
        ).most_common(),
        "missing_pair_prefixes": collections.Counter(
            (prefix(sub), prefix(sup)) for sub, sup in missing
        ).most_common(),
        "top_missing_subjects": subject_rows[:50],
        "top_missing_superclasses": missing_by_sup.most_common(50),
        "missing_frontier_rows": [
            {
                "subject": sub,
                "km": sorted(km_rows[sub]),
                "gold": sorted(gold_rows[sub]),
                "missing": sorted(missing_by_sub[sub]),
            }
            for sub in missing_frontier
        ],
        "top_gold_tail_witnesses": [
            {"sup": sup, "via": via, "subjects": count}
            for (sup, via), count in all_gold_tail_witnesses.most_common(100)
        ],
        "focus_rows": {
            name: {
                "km": sorted(km_rows[name]),
                "gold": sorted(gold_rows[name]),
                "missing": sorted(gold_rows[name] - km_rows[name]),
            }
            for name in focus
        },
        "first_two_hop_witnesses": [
            {"sub": sub, "sup": sup, "via": via}
            for (sub, sup), via in sorted(two_hop_witnesses.items())[:100]
        ],
        "first_missing": [list(pair) for pair in sorted(missing)[:100]],
        "first_extra": [list(pair) for pair in sorted(extra)[:100]],
    }
    with (args.output_dir / "diff-summary.json").open("w") as handle:
        json.dump(summary, handle, indent=2, sort_keys=True)
        handle.write("\n")
    with gzip.open(args.output_dir / "missing.tsv.gz", "wt") as handle:
        for sub, sup in sorted(missing):
            witness = two_hop_witnesses.get((sub, sup), "")
            handle.write(f"{sub}\t{sup}\t{witness}\n")
    with (args.output_dir / "missing-subjects.json").open("w") as handle:
        json.dump(subject_rows, handle, indent=2)
        handle.write("\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
