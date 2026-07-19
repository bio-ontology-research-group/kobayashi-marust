#!/usr/bin/env python3
"""Reconstruct and check the exact public taxonomy of ORE ontology 4669.

The independent OWLAPI projector replaces each private definition

    N_i == not (exists R_i.F_i)

with a fresh positive class

    P_i == exists R_i.F_i.

External complete reasoners classify that projected ontology.  Classical
complement duality gives P_i <= P_j iff N_j <= N_i.  A complete HermiT
disjoint-class query supplies every base-to-negative edge because
A <= N_i iff A and P_i are disjoint.  The structural certificate and an
isolated-element argument rule out negative-to-base edges, except the explicit
top/bottom cases handled below.

This checker preserves full IRIs, closes reasoner output transitively, writes a
standalone gzip TSV oracle, and requires exact equality with a candidate KM
JSON taxonomy when --candidate-km is supplied.
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Iterable


TOOLS = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(TOOLS))
from fingerprint_tail_fulliri import (  # noqa: E402
    BOTTOM,
    DECL_FUN,
    TOP,
    clean_iri,
    parse_output,
    strongly_connected_components,
)


PROXY_PREFIX = "urn:km:oracle:4669:positive-proxy:"


@dataclass(frozen=True)
class Mirror:
    negative: str
    proxy: str
    role: str
    filler: str


@dataclass
class Taxonomy:
    consistent: bool
    declared: set[str]
    unsat: set[str]
    pairs: set[tuple[str, str]]
    component: dict[str, int]
    reach: list[int]

    def entails(self, left: str, right: str) -> bool:
        if left == right:
            return left in self.component
        if left not in self.component or right not in self.component:
            return False
        left_component = self.component[left]
        right_component = self.component[right]
        return left_component == right_component or bool(
            self.reach[left_component] & (1 << right_component)
        )


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_declarations(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8", errors="strict")
    return {
        clean_iri(match.group(1))
        for match in DECL_FUN.finditer(text)
        if clean_iri(match.group(1)) not in (TOP, BOTTOM)
    }


def read_mapping(path: Path) -> list[Mirror]:
    lines = path.read_text(encoding="utf-8", errors="strict").splitlines()
    if not lines or lines[0] != "negative_iri\tproxy_iri\trole_iri\tfiller_iri":
        raise ValueError("unexpected proxy mapping header")
    mirrors: list[Mirror] = []
    for number, line in enumerate(lines[1:], 2):
        fields = line.split("\t")
        if len(fields) != 4 or any(not field for field in fields):
            raise ValueError(f"invalid mapping row {number}: {line!r}")
        mirrors.append(Mirror(*fields))
    if not mirrors:
        raise ValueError("empty proxy mapping")
    negatives = {mirror.negative for mirror in mirrors}
    proxies = {mirror.proxy for mirror in mirrors}
    if len(negatives) != len(mirrors) or len(proxies) != len(mirrors):
        raise ValueError("mapping is not one-to-one")
    if any(not proxy.startswith(PROXY_PREFIX) for proxy in proxies):
        raise ValueError("mapping contains a proxy outside the reserved namespace")
    return mirrors


def read_hermit_disjoint(
    path: Path,
    base: set[str],
    negatives: set[str],
) -> set[tuple[str, str]]:
    pairs: set[tuple[str, str]] = set()
    with gzip.open(path, "rt", encoding="utf-8", errors="strict") as handle:
        header = handle.readline().rstrip("\n")
        if header != "# km-4669-hermit-projected-disjoint-v1":
            raise ValueError("unexpected HermiT disjoint-oracle header")
        for number, raw_line in enumerate(handle, 2):
            line = raw_line.rstrip("\n")
            fields = line.split("\t")
            if len(fields) != 3 or fields[0] != "BASE_TO_NEGATIVE":
                raise ValueError(f"invalid HermiT disjoint row {number}: {line!r}")
            left, right = fields[1:]
            if left not in base:
                raise ValueError(
                    f"HermiT disjoint row {number} has non-base left class: {left}"
                )
            if right not in negatives:
                raise ValueError(
                    f"HermiT disjoint row {number} has non-negative right class: {right}"
                )
            pair = (left, right)
            if pair in pairs:
                raise ValueError(f"duplicate HermiT disjoint row {number}: {line!r}")
            pairs.add(pair)
    return pairs


def canonical_taxonomy(
    path: Path,
    output_format: str,
    declared: set[str],
) -> Taxonomy:
    consistent, edges, groups, explicit_unsat, output_declared = parse_output(
        path, output_format
    )
    declared = set(declared)
    declared.update(name for name in output_declared if name not in (TOP, BOTTOM))
    succ: dict[str, set[str]] = {}
    nodes = {TOP, BOTTOM, *declared, *explicit_unsat}

    def add(left: str, right: str) -> None:
        nodes.add(left)
        nodes.add(right)
        if left != right:
            succ.setdefault(left, set()).add(right)

    for left, right in edges:
        add(clean_iri(left), clean_iri(right))
    for group in groups:
        for index, left in enumerate(group):
            for right in group[index + 1 :]:
                add(left, right)
                add(right, left)
    for name in explicit_unsat:
        add(name, BOTTOM)
    for name in declared:
        add(name, TOP)

    component, components = strongly_connected_components(nodes, succ)
    component_succ: list[set[int]] = [set() for _ in components]
    component_pred: list[set[int]] = [set() for _ in components]
    for left, rights in succ.items():
        left_component = component[left]
        for right in rights:
            right_component = component[right]
            if left_component != right_component:
                component_succ[left_component].add(right_component)
                component_pred[right_component].add(left_component)

    unsat_components = {component[BOTTOM]}
    stack = list(unsat_components)
    while stack:
        current = stack.pop()
        for predecessor in component_pred[current]:
            if predecessor not in unsat_components:
                unsat_components.add(predecessor)
                stack.append(predecessor)
    if component[TOP] in unsat_components:
        consistent = False
    unsat = {
        name
        for component_id in unsat_components
        for name in components[component_id]
        if name in declared
    }

    indegree = [0] * len(components)
    for rights in component_succ:
        for right in rights:
            indegree[right] += 1
    ready = deque(index for index, degree in enumerate(indegree) if degree == 0)
    specific_to_general: list[int] = []
    while ready:
        current = ready.popleft()
        specific_to_general.append(current)
        for right in component_succ[current]:
            indegree[right] -= 1
            if indegree[right] == 0:
                ready.append(right)
    if len(specific_to_general) != len(components):
        raise RuntimeError("SCC condensation unexpectedly contains a cycle")

    general_to_specific = list(reversed(specific_to_general))
    remap = {old: new for new, old in enumerate(general_to_specific)}
    remapped_succ: list[list[int]] = [[] for _ in components]
    remapped_members: list[list[str]] = [[] for _ in components]
    remapped_component: dict[str, int] = {}
    for new, old in enumerate(general_to_specific):
        remapped_succ[new] = [remap[right] for right in component_succ[old]]
        remapped_members[new] = sorted(
            name for name in components[old] if name in declared and name not in unsat
        )
        for name in components[old]:
            remapped_component[name] = new

    reach = [0] * len(remapped_succ)
    for current, rights in enumerate(remapped_succ):
        bits = 0
        for right in rights:
            if right >= current:
                raise RuntimeError("component order does not place supers first")
            bits |= (1 << right) | reach[right]
        reach[current] = bits

    pairs: set[tuple[str, str]] = set()
    for left in sorted(declared - unsat):
        component_id = remapped_component[left]
        for right in remapped_members[component_id]:
            if right != left:
                pairs.add((left, right))
        bits = reach[component_id]
        while bits:
            least = bits & -bits
            for right in remapped_members[least.bit_length() - 1]:
                if right != left:
                    pairs.add((left, right))
            bits ^= least

    return Taxonomy(
        consistent=bool(consistent),
        declared=declared,
        unsat=unsat,
        pairs=pairs,
        component=remapped_component,
        reach=reach,
    )


def pair_digest(pairs: Iterable[tuple[str, str]], unsat: Iterable[str]) -> str:
    digest = hashlib.sha256()
    digest.update(b"consistent\x01")
    for left, right in sorted(pairs):
        digest.update(b"P")
        for value in (left, right):
            encoded = value.encode("utf-8")
            digest.update(len(encoded).to_bytes(8, "big"))
            digest.update(encoded)
    for name in sorted(unsat):
        digest.update(b"U")
        encoded = name.encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
    return digest.hexdigest()


def region_counts(
    pairs: set[tuple[str, str]],
    base: set[str],
    negative: set[str],
) -> dict[str, int]:
    counts = {"base_base": 0, "base_negative": 0, "negative_base": 0, "negative_negative": 0}
    for left, right in pairs:
        left_region = "base" if left in base else "negative"
        right_region = "base" if right in base else "negative"
        counts[f"{left_region}_{right_region}"] += 1
    return counts


def write_expected(
    path: Path,
    pairs: set[tuple[str, str]],
    unsat: set[str],
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(path, "wt", encoding="utf-8", newline="\n") as handle:
        handle.write("# km-4669-private-negative-existential-oracle-v2\n")
        for left, right in sorted(pairs):
            handle.write(f"PAIR\t{left}\t{right}\n")
        for name in sorted(unsat):
            handle.write(f"UNSAT\t{name}\n")


def sample(values: set[tuple[str, str]] | set[str], limit: int = 20):
    return list(sorted(values))[:limit]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--projected", type=Path, required=True)
    parser.add_argument("--mapping", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--konclude-taxonomy", type=Path, required=True)
    parser.add_argument("--hermit-disjoint", type=Path, required=True)
    parser.add_argument("--hermit-disjoint-summary", type=Path, required=True)
    parser.add_argument("--elk-taxonomy", type=Path)
    parser.add_argument("--candidate-km", type=Path)
    parser.add_argument("--expected-tsv", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    certificate = json.loads(args.certificate.read_text(encoding="utf-8"))
    if certificate.get("certificate") != "private-negative-existential-projection-v2":
        raise ValueError("unexpected structural certificate kind")
    if certificate.get("passed") is not True:
        raise ValueError("structural certificate did not pass")
    required_contract = {
        "negative_names_private": True,
        "remaining_tbox_positive_el_plus_named_disjointness": True,
        "no_top_gci_or_bottom_constructor": True,
        "no_reflexive_or_universal_role": True,
        "base_to_negative_requires_disjoint_oracle": True,
        "negative_to_base_absent_by_isolated_element": True,
    }
    if certificate.get("cross_region_contract") != required_contract:
        raise ValueError("unexpected or incomplete cross-region contract")
    for key, path in (
        ("source_sha256", args.source),
        ("projected_sha256", args.projected),
        ("mapping_sha256", args.mapping),
    ):
        actual = sha256_file(path)
        if certificate.get(key) != actual:
            raise ValueError(f"{key} mismatch: certificate={certificate.get(key)} actual={actual}")

    mirrors = read_mapping(args.mapping)
    if len(mirrors) != certificate.get("negative_mirrors"):
        raise ValueError("mapping/certificate mirror count differs")
    negatives = {mirror.negative for mirror in mirrors}
    proxies = {mirror.proxy for mirror in mirrors}
    negative_of_proxy = {mirror.proxy: mirror.negative for mirror in mirrors}

    source_public = parse_declarations(args.source)
    projected_public = parse_declarations(args.projected)
    if len(source_public) != certificate.get("source_declared_classes"):
        raise ValueError("source declaration count differs from certificate")
    if len(projected_public) != certificate.get("projected_declared_classes"):
        raise ValueError("projected declaration count differs from certificate")
    if not negatives <= source_public:
        raise ValueError("mapping contains an undeclared source negative class")
    base = source_public - negatives
    if projected_public != base | proxies:
        missing = (base | proxies) - projected_public
        extra = projected_public - (base | proxies)
        raise ValueError(
            f"projected declaration universe differs: missing={sample(missing)} extra={sample(extra)}"
        )

    disjoint_summary = json.loads(
        args.hermit_disjoint_summary.read_text(encoding="utf-8")
    )
    if disjoint_summary.get("oracle") != "km-4669-hermit-projected-disjoint-v1":
        raise ValueError("unexpected HermiT disjoint-oracle kind")
    if disjoint_summary.get("consistent") is not True:
        raise ValueError("HermiT disjoint-oracle projection was not consistent")
    if disjoint_summary.get("witness_failures") != 0:
        raise ValueError("HermiT disjoint-oracle witness recheck failed")
    if not isinstance(disjoint_summary.get("witness_rechecks"), int):
        raise ValueError("HermiT disjoint-oracle witness count is missing")
    for key, path in (
        ("projected_sha256", args.projected),
        ("mapping_sha256", args.mapping),
        ("cross_tsv_sha256", args.hermit_disjoint),
    ):
        actual = sha256_file(path)
        if disjoint_summary.get(key) != actual:
            raise ValueError(
                f"HermiT {key} mismatch: summary={disjoint_summary.get(key)} actual={actual}"
            )
    base_negative_oracle = read_hermit_disjoint(
        args.hermit_disjoint, base, negatives
    )
    if disjoint_summary.get("cross_edges") != len(base_negative_oracle):
        raise ValueError("HermiT cross-edge TSV/summary count differs")
    if disjoint_summary.get("proxies") != len(mirrors):
        raise ValueError("HermiT proxy count differs from mapping")
    if disjoint_summary.get("base_classes") != len(base):
        raise ValueError("HermiT base-class count differs from source")

    projected = canonical_taxonomy(args.konclude_taxonomy, "owlxml", projected_public)
    if not projected.consistent:
        raise ValueError("Konclude reports the positive projection inconsistent")

    corroboration: dict[str, object] | None = None
    if args.elk_taxonomy:
        elk = canonical_taxonomy(args.elk_taxonomy, "functional", projected_public)
        elk_missing = projected.pairs - elk.pairs
        elk_extra = elk.pairs - projected.pairs
        elk_unsat_missing = projected.unsat - elk.unsat
        elk_unsat_extra = elk.unsat - projected.unsat
        corroboration = {
            "status": "match" if not (
                elk_missing or elk_extra or elk_unsat_missing or elk_unsat_extra
            ) else "diff",
            "pairs": len(elk.pairs),
            "unsatisfiable": len(elk.unsat),
            "missing_pairs": len(elk_missing),
            "extra_pairs": len(elk_extra),
            "missing_unsatisfiable": len(elk_unsat_missing),
            "extra_unsatisfiable": len(elk_unsat_extra),
            "missing_sample": sample(elk_missing),
            "extra_sample": sample(elk_extra),
        }
        if corroboration["status"] != "match":
            raise ValueError(f"ELK/Konclude projected taxonomy disagreement: {corroboration}")

    base_unsat = projected.unsat & base
    proxy_unsat = projected.unsat & proxies
    base_top = {name for name in base if projected.entails(TOP, name)}
    proxy_top = {name for name in proxies if projected.entails(TOP, name)}
    negative_unsat = {negative_of_proxy[proxy] for proxy in proxy_top}
    negative_top = {negative_of_proxy[proxy] for proxy in proxy_unsat}
    expected_unsat = base_unsat | negative_unsat

    expected_pairs: set[tuple[str, str]] = {
        (left, right)
        for left, right in projected.pairs
        if left in base and right in base
    }
    # Complement duality. This includes P_C <= P_Thing, whose filler-side
    # analogue C <= owl:Thing is normally suppressed by public taxonomies.
    for left, right in projected.pairs:
        if left in proxies and right in proxies:
            negative_left = negative_of_proxy[right]
            negative_right = negative_of_proxy[left]
            if negative_left not in expected_unsat and negative_left != negative_right:
                expected_pairs.add((negative_left, negative_right))

    # Exact cross-region recovery.  In the original ontology N_i == not P_i,
    # so a named base class A is below N_i exactly when A and P_i are disjoint
    # in the conservative positive projection.  HermiT reports that complete
    # named disjointness relation.  Canonical taxonomies omit unsatisfiable
    # left-hand classes, which are filtered here.
    canonical_base_negative = {
        (left, right)
        for left, right in base_negative_oracle
        if left not in expected_unsat and right not in expected_unsat
    }
    expected_pairs.update(canonical_base_negative)

    public_satisfiable = source_public - expected_unsat
    # P == bottom makes N == top. Public named aliases of top are retained as
    # superclasses even though owl:Thing itself is omitted.
    for top_negative in negative_top:
        for left in public_satisfiable:
            if left != top_negative:
                expected_pairs.add((left, top_negative))
    # A source base class equivalent to top is unlikely under the certificate,
    # but handling it makes the reconstruction total rather than assumption-led.
    for top_base in base_top:
        for left in negatives - expected_unsat:
            if left != top_base:
                expected_pairs.add((left, top_base))

    thing_mirrors = [mirror for mirror in mirrors if mirror.filler == TOP]
    if len(thing_mirrors) != 1:
        raise ValueError(f"expected exactly one owl:Thing filler mirror, got {len(thing_mirrors)}")
    thing_proxy = thing_mirrors[0].proxy
    thing_negative = thing_mirrors[0].negative
    proxy_to_thing = {
        proxy for proxy in proxies
        if proxy != thing_proxy and projected.entails(proxy, thing_proxy)
    }
    reversed_from_thing = {
        right for left, right in expected_pairs if left == thing_negative and right in negatives
    }
    if {negative_of_proxy[proxy] for proxy in proxy_to_thing} != reversed_from_thing:
        raise ValueError("P_C <= P_Thing reversal is incomplete")

    write_expected(args.expected_tsv, expected_pairs, expected_unsat)
    expected_sha = pair_digest(expected_pairs, expected_unsat)
    report: dict[str, object] = {
        "schema_version": 1,
        "oracle": "km-4669-private-negative-existential-oracle-v2",
        "status": "oracle-built",
        "source": str(args.source),
        "source_sha256": sha256_file(args.source),
        "projected": str(args.projected),
        "projected_sha256": sha256_file(args.projected),
        "mapping": str(args.mapping),
        "mapping_sha256": sha256_file(args.mapping),
        "certificate": str(args.certificate),
        "certificate_sha256": sha256_file(args.certificate),
        "hermit_disjoint": str(args.hermit_disjoint),
        "hermit_disjoint_sha256": sha256_file(args.hermit_disjoint),
        "hermit_disjoint_summary": str(args.hermit_disjoint_summary),
        "hermit_disjoint_summary_sha256": sha256_file(args.hermit_disjoint_summary),
        "hermit_disjoint_raw_edges": len(base_negative_oracle),
        "hermit_disjoint_canonical_edges": len(canonical_base_negative),
        "hermit_disjoint_proxies_with_edges": disjoint_summary.get(
            "proxies_with_cross_edges"
        ),
        "hermit_disjoint_sample": disjoint_summary.get("sample"),
        "konclude_taxonomy": str(args.konclude_taxonomy),
        "konclude_taxonomy_sha256": sha256_file(args.konclude_taxonomy),
        "source_public_classes": len(source_public),
        "base_classes": len(base),
        "negative_classes": len(negatives),
        "projected_pairs": len(projected.pairs),
        "projected_unsatisfiable": len(projected.unsat),
        "base_unsatisfiable": len(base_unsat),
        "proxy_unsatisfiable": len(proxy_unsat),
        "base_equivalent_top": len(base_top),
        "proxy_equivalent_top": len(proxy_top),
        "expected_pairs": len(expected_pairs),
        "expected_unsatisfiable": len(expected_unsat),
        "expected_region_counts": region_counts(expected_pairs, base, negatives),
        "expected_taxonomy_sha256": expected_sha,
        "expected_tsv": str(args.expected_tsv),
        "expected_tsv_sha256": sha256_file(args.expected_tsv),
        "owl_thing_proxy_subclasses": len(proxy_to_thing),
        "owl_thing_negative_subsumers": len(reversed_from_thing),
        "elk_corroboration": corroboration,
    }

    exit_code = 0
    if args.candidate_km:
        candidate = canonical_taxonomy(args.candidate_km, "json", source_public)
        unknown = {
            name for name in candidate.component
            if name not in source_public and name not in (TOP, BOTTOM)
        }
        missing_pairs = expected_pairs - candidate.pairs
        extra_pairs = candidate.pairs - expected_pairs
        missing_unsat = expected_unsat - candidate.unsat
        extra_unsat = candidate.unsat - expected_unsat
        matched = (
            candidate.consistent
            and not unknown
            and not missing_pairs
            and not extra_pairs
            and not missing_unsat
            and not extra_unsat
        )
        report["candidate"] = {
            "path": str(args.candidate_km),
            "sha256": sha256_file(args.candidate_km),
            "consistent": candidate.consistent,
            "pairs": len(candidate.pairs),
            "unsatisfiable": len(candidate.unsat),
            "taxonomy_sha256": pair_digest(candidate.pairs, candidate.unsat),
            "region_counts": region_counts(candidate.pairs, base, negatives),
            "unknown_names": len(unknown),
            "unknown_sample": sample(unknown),
            "missing_pairs": len(missing_pairs),
            "missing_pair_sample": sample(missing_pairs),
            "extra_pairs": len(extra_pairs),
            "extra_pair_sample": sample(extra_pairs),
            "missing_unsatisfiable": len(missing_unsat),
            "missing_unsatisfiable_sample": sample(missing_unsat),
            "extra_unsatisfiable": len(extra_unsat),
            "extra_unsatisfiable_sample": sample(extra_unsat),
            "verdict": "match" if matched else "diff",
        }
        report["status"] = "match" if matched else "diff"
        exit_code = 0 if matched else 1

    args.report.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(args.report) + ".tmp")
    temporary.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(args.report)
    print(json.dumps(report, sort_keys=True))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
