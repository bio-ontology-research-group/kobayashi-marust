#!/usr/bin/env python3
"""Deterministically partition the ORE corpus into size-balanced ontology jobs.

Each ontology, not each reasoner run, is the indivisible unit. A Slurm task
therefore measures the complete rotated mechanism/baseline panel for every
ontology assigned to it on one CPU model. The capacity constraint keeps 592
ontologies in 50 shards of exactly 11 or 12 ontologies, while longest-processing
time placement disperses the largest and structurally hardest inputs.
"""

import argparse
import csv


def number(row, key):
    try:
        return int(float(row.get(key, 0) or 0))
    except ValueError:
        return 0


def estimated_weight(row):
    """Source-only scheduling weight; never used as a routing feature or label."""
    return (
        number(row, "source.file_bytes")
        + 64 * number(row, "source.concept_expressions")
        + 64 * number(row, "clauses.clauses")
        + 4096 * number(row, "clauses.disjunctive_clauses")
        + 4096 * number(row, "source.unions")
        + 1024
        * (
            number(row, "source.min_cardinalities")
            + number(row, "source.max_cardinalities")
            + number(row, "source.exact_cardinalities")
        )
    )


def partition(rows, shard_count):
    if shard_count <= 0 or shard_count > len(rows):
        raise ValueError("shard count must be between one and the ontology count")
    base, remainder = divmod(len(rows), shard_count)
    capacities = [base + (index < remainder) for index in range(shard_count)]
    assignments = [[] for _ in range(shard_count)]
    weights = [0] * shard_count
    global_index = {
        row["ont"]: index for index, row in enumerate(sorted(rows, key=lambda r: r["ont"]))
    }
    for row in sorted(rows, key=lambda r: (-estimated_weight(r), r["ont"])):
        candidates = [
            index
            for index in range(shard_count)
            if len(assignments[index]) < capacities[index]
        ]
        shard = min(candidates, key=lambda index: (weights[index], len(assignments[index]), index))
        weight = estimated_weight(row)
        assignments[shard].append((global_index[row["ont"]], row["ont"], weight))
        weights[shard] += weight
    for shard in assignments:
        shard.sort()
    return assignments, weights


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--profiles", required=True)
    parser.add_argument("--shards", type=int, default=50)
    parser.add_argument("--task", type=int)
    parser.add_argument("--summary", action="store_true")
    args = parser.parse_args()
    with open(args.profiles, newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    if not rows or any(not row.get("ont") for row in rows):
        raise SystemExit("profile table is empty or lacks ontology names")
    assignments, weights = partition(rows, args.shards)
    if args.summary:
        for index, shard in enumerate(assignments):
            print(f"{index}\t{len(shard)}\t{weights[index]}")
        return
    selected = range(args.shards) if args.task is None else [args.task]
    for shard_index in selected:
        if not 0 <= shard_index < args.shards:
            raise SystemExit(f"task index {shard_index} outside 0..{args.shards - 1}")
        for index, ontology, weight in assignments[shard_index]:
            print(f"{shard_index}\t{index}\t{weight}\t{ontology}")


if __name__ == "__main__":
    main()
