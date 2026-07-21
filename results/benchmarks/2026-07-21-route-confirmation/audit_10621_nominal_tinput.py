#!/usr/bin/env python3
"""Audit the nominal provenance in the saved ORE 10621 bridge TInput.

This is a read-only diagnostic.  It does not run a reasoner and it never
constitutes acceptance evidence.
"""

from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
from typing import Any, Iterator


def short(name: str) -> str:
    return name.rsplit("#", 1)[-1].rsplit("/", 1)[-1]


def nominal_values(value: Any) -> Iterator[str]:
    if isinstance(value, dict):
        for key, child in value.items():
            if key == "Nominal" and isinstance(child, str):
                yield child
            yield from nominal_values(child)
    elif isinstance(value, list):
        for child in value:
            yield from nominal_values(child)


def atom_concept(atom: dict[str, Any]) -> int | None:
    return atom.get("c") if atom.get("k") in {"c", "e"} else None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("tin", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    with args.tin.open(encoding="utf-8") as stream:
        tin = json.load(stream)

    concepts: list[str] = tin["concepts"]
    proxy_ids = {
        index: name
        for index, name in enumerate(concepts)
        if short(name).startswith("__nom__")
    }
    source_axiom_nominals: list[dict[str, Any]] = []
    source_occurrences: collections.Counter[str] = collections.Counter()
    for index, axiom in enumerate(tin.get("source_axioms", [])):
        values = list(nominal_values(axiom))
        if not values:
            continue
        source_occurrences.update(values)
        source_axiom_nominals.append(
            {
                "index": index,
                "kind": axiom.get("kind"),
                "occurrences": values,
            }
        )

    clause_shape_histogram: collections.Counter[str] = collections.Counter()
    proxy_clause_counts: collections.Counter[str] = collections.Counter()
    simple_proxy_implications: collections.Counter[tuple[str, str]] = collections.Counter()
    clauses_with_proxy = 0
    for clause in tin.get("clauses", []):
        body = clause.get("body", [])
        head = clause.get("head", [])
        ids = {
            concept
            for atom in body + head
            if (concept := atom_concept(atom)) in proxy_ids
        }
        if not ids:
            continue
        clauses_with_proxy += 1
        shape = (
            "+".join(sorted(atom.get("k", "?") for atom in body))
            + "->"
            + "+".join(sorted(atom.get("k", "?") for atom in head))
        )
        clause_shape_histogram[shape] += 1
        for concept in ids:
            proxy_clause_counts[proxy_ids[concept]] += 1
        if (
            len(body) == 1
            and body[0].get("k") == "c"
            and body[0].get("c") in proxy_ids
            and not body[0].get("neg", False)
            and len(head) == 1
            and head[0].get("k") == "c"
            and head[0].get("t") == body[0].get("t")
            and not head[0].get("neg", False)
        ):
            simple_proxy_implications[
                (proxy_ids[body[0]["c"]], concepts[head[0]["c"]])
            ] += 1

    proxy_suffixes = {short(name).removeprefix("__nom__") for name in proxy_ids.values()}
    source_names = set(source_occurrences)
    report = {
        "schema_version": 1,
        "acceptance_evidence": False,
        "tin": str(args.tin),
        "concept_count": len(concepts),
        "source_axiom_count": len(tin.get("source_axioms", [])),
        "nominal_proxy_count": len(proxy_ids),
        "source_nominal_unique_count": len(source_names),
        "source_nominal_occurrence_count": sum(source_occurrences.values()),
        "source_axioms_with_nominals": len(source_axiom_nominals),
        "source_nominal_names_missing_proxy": sorted(source_names - proxy_suffixes),
        "proxy_suffixes_missing_source_nominal": sorted(proxy_suffixes - source_names),
        "source_nominal_occurrences": dict(sorted(source_occurrences.items())),
        "source_axiom_nominals": source_axiom_nominals,
        "clauses_with_nominal_proxy": clauses_with_proxy,
        "nominal_clause_shape_histogram": dict(sorted(clause_shape_histogram.items())),
        "nominal_proxy_clause_counts": dict(sorted(proxy_clause_counts.items())),
        "simple_proxy_implications": [
            {"proxy": proxy, "head": head, "count": count}
            for (proxy, head), count in sorted(simple_proxy_implications.items())
        ],
    }
    with args.output.open("w", encoding="utf-8") as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write("\n")


if __name__ == "__main__":
    main()
