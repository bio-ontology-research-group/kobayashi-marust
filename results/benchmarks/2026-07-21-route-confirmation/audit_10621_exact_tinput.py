#!/usr/bin/env python3
"""Fail-closed source-to-TInput audit for the ORE 10621 nominal ABox.

The taxonomy comparison establishes semantic correctness.  This independent
audit establishes that the named ``ht_bridge`` route received an exact typed
representation of every source ClassAssertion and DifferentIndividuals pair.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re


ABOX_NAMES = (
    "ClassAssertion",
    "ObjectPropertyAssertion",
    "NegativeObjectPropertyAssertion",
    "DataPropertyAssertion",
    "NegativeDataPropertyAssertion",
    "SameIndividual",
    "DifferentIndividuals",
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def iri_local_name(iri: str) -> str:
    """Mirror the collision-free case of the frontend's IRI registry."""
    return iri.rsplit("#", 1)[-1].rsplit("/", 1)[-1]


def source_abox(path: Path) -> tuple[list[str], list[tuple[str, str]], dict[str, int]]:
    asserted: list[str] = []
    different_groups: list[list[str]] = []
    counts = {name: 0 for name in ABOX_NAMES}
    start = re.compile(r"^\s*(" + "|".join(ABOX_NAMES) + r")\(")
    class_assertion = re.compile(r"^\s*ClassAssertion\(owl:Thing\s+<([^>]+)>\)\s*$")
    different = re.compile(r"^\s*DifferentIndividuals\((.*)\)\s*$")
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            match = start.match(line)
            if not match:
                continue
            kind = match.group(1)
            counts[kind] += 1
            if kind == "ClassAssertion":
                parsed = class_assertion.match(line)
                if not parsed:
                    raise ValueError(
                        f"unsupported ClassAssertion syntax on line {line_number}"
                    )
                asserted.append(parsed.group(1))
            elif kind == "DifferentIndividuals":
                parsed = different.match(line)
                if not parsed:
                    raise ValueError(
                        f"unsupported DifferentIndividuals syntax on line {line_number}"
                    )
                names = re.findall(r"<([^>]+)>", parsed.group(1))
                if not names:
                    raise ValueError(
                        f"empty DifferentIndividuals axiom on line {line_number}"
                    )
                different_groups.append(names)

    pairs = {
        tuple(sorted(pair))
        for group in different_groups
        for pair in itertools.combinations(group, 2)
    }
    return asserted, sorted(pairs), counts


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tin", type=Path, required=True)
    parser.add_argument("--ontology", type=Path, required=True)
    parser.add_argument("--ontology-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    ontology_sha256 = sha256_file(args.ontology)
    tin_sha256 = sha256_file(args.tin)
    asserted, source_pairs, source_counts = source_abox(args.ontology)
    tin = json.loads(args.tin.read_text(encoding="utf-8"))
    meta = tin.get("nominal_abox") or {}
    entries = meta.get("individuals") or []
    individuals = [entry.get("individual") for entry in entries]
    proxies = [proxy for entry in entries for proxy in (entry.get("proxies") or [])]
    assertions = [
        assertion
        for entry in entries
        for assertion in (entry.get("assertions") or [])
    ]
    actual_pairs = [tuple(pair) for pair in (meta.get("different") or [])]
    concepts = tin.get("concepts") or []
    concept_ids = {name: index for index, name in enumerate(concepts)}
    nominal_ids = tin.get("nominals") or []
    source_internal = {name: iri_local_name(name) for name in asserted}
    expected_individuals = sorted(source_internal.values())
    expected_pairs = sorted(
        tuple(sorted((source_internal[left], source_internal[right])))
        for left, right in source_pairs
    )
    expected_proxy_ids = sorted(concept_ids[p] for p in proxies if p in concept_ids)

    unsupported_source_count = sum(
        count
        for name, count in source_counts.items()
        if name not in {"ClassAssertion", "DifferentIndividuals"}
    )
    checks = {
        "ontology_sha256": ontology_sha256 == args.ontology_sha256,
        "source_has_85_class_assertions": source_counts["ClassAssertion"] == 85,
        "source_has_one_different_axiom": source_counts["DifferentIndividuals"] == 1,
        "source_has_no_other_abox_axioms": unsupported_source_count == 0,
        "source_assertion_individuals_unique": len(asserted) == len(set(asserted)),
        "source_different_is_complete_85_clique": len(expected_pairs) == 3570
        and {name for pair in expected_pairs for name in pair}
        == set(expected_individuals),
        "metadata_complete": meta.get("complete") is True,
        # Empty vectors are omitted by serde's skip_serializing_if.
        "metadata_unsupported_empty": not meta.get("unsupported"),
        "metadata_has_85_individuals": len(entries) == 85,
        "metadata_individuals_sorted_unique": individuals
        == sorted(set(individuals)),
        "metadata_individuals_match_source": individuals == expected_individuals,
        "source_local_names_collision_free": len(source_internal)
        == len(set(source_internal.values())),
        "one_unique_proxy_per_individual": len(proxies) == 85
        and len(proxies) == len(set(proxies))
        and all(len(entry.get("proxies") or []) == 1 for entry in entries),
        "one_top_assertion_per_individual": len(assertions) == 85
        and all(
            entry.get("assertions") == ["Top"]
            for entry in entries
        ),
        "all_proxies_are_concepts": len(expected_proxy_ids) == len(proxies),
        "proxy_names_bind_their_individuals": all(
            entry.get("proxies") == [f"__nom__{entry.get('individual')}"]
            for entry in entries
        ),
        # cb_to_ht clears the legacy fast-tableau vector on inverse-role input.
        # The native bridge consumes nominal_abox directly and independently
        # validates every proxy id (bridge.rs::native_nominal_metadata_covered).
        "legacy_nominal_vector_cleared_by_inverse_fence": nominal_ids == [],
        "metadata_has_3570_different_pairs": len(actual_pairs) == 3570,
        "metadata_different_pairs_sorted_unique": actual_pairs
        == sorted(set(actual_pairs)),
        "metadata_different_pairs_match_source": actual_pairs == expected_pairs,
    }
    record = {
        "schema_version": 1,
        "scope": "source-to-typed-tinput-nominal-abox-coverage",
        "status": "verified_exact" if all(checks.values()) else "mismatch",
        "supports_acceptance": all(checks.values()),
        "checks": checks,
        "ontology": str(args.ontology),
        "ontology_sha256": ontology_sha256,
        "tinput": str(args.tin),
        "tinput_sha256": tin_sha256,
        "source_abox_counts": source_counts,
        "source_individual_count": len(asserted),
        "source_different_pair_count": len(expected_pairs),
        "metadata_individual_count": len(entries),
        "metadata_proxy_count": len(proxies),
        "metadata_assertion_count": len(assertions),
        "metadata_different_pair_count": len(actual_pairs),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(args.output)
    return 0 if record["status"] == "verified_exact" else 1


if __name__ == "__main__":
    raise SystemExit(main())
