#!/usr/bin/env python3
"""Fingerprint a full-panel named-class taxonomy without local-name collisions.

The ORE local-name canonicalizer is not injective for 3524/15703: generated
class IRIs contain another full IRI after a slash, so unrelated named classes
collapse to the same final fragment. This tool preserves complete IRIs, computes
the SCC-condensed transitive closure with integer bitsets, and hashes the exact
sorted relation without materializing it as a file.
"""

from __future__ import annotations

import argparse
from collections import deque
import gzip
import hashlib
import json
from pathlib import Path
import re
import resource
import time


TOP = "http://www.w3.org/2002/07/owl#Thing"
BOTTOM = "http://www.w3.org/2002/07/owl#Nothing"

SUBCLASS_FUN = re.compile(
    r"SubClassOf\(\s*(<[^>]+>|[\w:]+)\s+(<[^>]+>|[\w:]+)\s*\)"
)
EQUIV_FUN = re.compile(r"EquivalentClasses\(\s*([^)]+?)\s*\)")
TOKEN_FUN = re.compile(r"<[^>]+>|[A-Za-z][\w:.\-]*")
DECL_FUN = re.compile(
    r"Declaration\(\s*Class\(\s*(<[^>]+>|[\w:]+)\s*\)\s*\)"
)
SUBCLASS_XML = re.compile(
    r'<SubClassOf>\s*<Class\s+IRI="([^"]+)"\s*/>\s*'
    r'<Class\s+IRI="([^"]+)"\s*/>\s*</SubClassOf>',
    re.S,
)
EQUIV_XML = re.compile(r"<EquivalentClasses>(.*?)</EquivalentClasses>", re.S)
CLASS_IRI = re.compile(r'<Class\s+IRI="([^"]+)"\s*/>')
DECL_XML = re.compile(
    r'<Declaration>\s*<Class\s+IRI="([^"]+)"\s*/>\s*</Declaration>', re.S
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def clean_iri(value: str) -> str:
    value = value.strip()
    if value.startswith("<") and value.endswith(">"):
        value = value[1:-1]
    if value in ("owl:Thing", "Thing", "thing"):
        return TOP
    if value in ("owl:Nothing", "Nothing", "nothing"):
        return BOTTOM
    return value


def parse_output(path: Path, output_format: str):
    text = path.read_text(encoding="utf-8", errors="replace")
    if output_format == "json":
        data = json.loads(text)
        return (
            bool(data.get("consistent", True)),
            [(clean_iri(a), clean_iri(b)) for a, b in data.get("subsumptions", [])],
            [],
            {clean_iri(name) for name in data.get("unsatisfiable", [])},
            set(),
        )
    if output_format == "functional":
        edges = [
            (clean_iri(match.group(1)), clean_iri(match.group(2)))
            for match in SUBCLASS_FUN.finditer(text)
        ]
        groups = [
            [clean_iri(token) for token in TOKEN_FUN.findall(match.group(1))]
            for match in EQUIV_FUN.finditer(text)
        ]
        groups = [group for group in groups if len(group) >= 2]
        declared = {clean_iri(match.group(1)) for match in DECL_FUN.finditer(text)}
        return True, edges, groups, set(), declared
    edges = [
        (clean_iri(match.group(1)), clean_iri(match.group(2)))
        for match in SUBCLASS_XML.finditer(text)
    ]
    groups = [
        [clean_iri(value) for value in CLASS_IRI.findall(match.group(1))]
        for match in EQUIV_XML.finditer(text)
    ]
    groups = [group for group in groups if len(group) >= 2]
    declared = {clean_iri(match.group(1)) for match in DECL_XML.finditer(text)}
    return True, edges, groups, set(), declared


def parse_source_declarations(path: Path) -> set[str]:
    declared: set[str] = set()
    with path.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            declared.update(
                clean_iri(match.group(1)) for match in DECL_FUN.finditer(line)
            )
    return declared


def strongly_connected_components(nodes: set[str], succ: dict[str, set[str]]):
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    on_stack: set[str] = set()
    stack: list[str] = []
    component: dict[str, int] = {}
    components: list[list[str]] = []
    counter = 0
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(succ.get(root, ())))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on_stack.add(root)
        while work:
            current, iterator = work[-1]
            advanced = False
            for target in iterator:
                if target not in index:
                    index[target] = low[target] = counter
                    counter += 1
                    stack.append(target)
                    on_stack.add(target)
                    work.append((target, iter(succ.get(target, ()))))
                    advanced = True
                    break
                if target in on_stack:
                    low[current] = min(low[current], index[target])
            if advanced:
                continue
            if low[current] == index[current]:
                members = []
                while True:
                    member = stack.pop()
                    on_stack.discard(member)
                    component[member] = len(components)
                    members.append(member)
                    if member == current:
                        break
                components.append(members)
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[current])
    return component, components


def frame(digest, value: str) -> None:
    encoded = value.encode("utf-8")
    digest.update(len(encoded).to_bytes(8, "big"))
    digest.update(encoded)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--format", choices=("json", "functional", "owlxml"), required=True)
    parser.add_argument("--source-ontology", type=Path)
    parser.add_argument("--output-prefix", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    started = time.monotonic()
    consistent, edges, groups, input_unsat, declared = parse_output(
        args.input, args.format
    )
    source_edges = len(edges)
    source_groups = len(groups)
    source_declared = len(declared)
    ontology_declared: set[str] = set()
    if args.source_ontology:
        ontology_declared = parse_source_declarations(args.source_ontology)
        declared.update(ontology_declared)

    if not consistent:
        edges = []
        groups = []
        input_unsat = set()
        declared = set()

    succ: dict[str, set[str]] = {}
    nodes: set[str] = set()

    def add(left: str, right: str) -> None:
        nodes.add(left)
        nodes.add(right)
        if left != right:
            succ.setdefault(left, set()).add(right)

    for left, right in edges:
        add(left, right)
    del edges
    for group in groups:
        representative = group[0]
        nodes.update(group)
        for name in group[1:]:
            add(name, representative)
            add(representative, name)
    del groups

    unsat = set(input_unsat)
    nodes.update(unsat)
    nodes.update(declared)
    for name in list(nodes):
        if name not in (TOP, BOTTOM):
            add(name, TOP)

    if nodes:
        component, components = strongly_connected_components(nodes, succ)
    else:
        component, components = {}, []
    del nodes

    component_succ: list[set[int]] = [set() for _ in components]
    component_pred: list[set[int]] = [set() for _ in components]
    for left, rights in succ.items():
        left_component = component[left]
        for right in rights:
            right_component = component[right]
            if left_component != right_component:
                component_succ[left_component].add(right_component)
                component_pred[right_component].add(left_component)
    del succ

    bottom_components = {component[BOTTOM]} if BOTTOM in component else set()
    unsat_components = set(bottom_components)
    stack = list(bottom_components)
    while stack:
        current = stack.pop()
        for predecessor in component_pred[current]:
            if predecessor not in unsat_components:
                unsat_components.add(predecessor)
                stack.append(predecessor)
    if TOP in component and component[TOP] in unsat_components:
        consistent = False
    for component_id in unsat_components:
        unsat.update(name for name in components[component_id] if name != BOTTOM)

    if consistent:
        indegree = [0] * len(components)
        for rights in component_succ:
            for right in rights:
                indegree[right] += 1
        ready = deque(index for index, degree in enumerate(indegree) if degree == 0)
        specific_to_general = []
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
        for new, old in enumerate(general_to_specific):
            remapped_succ[new] = [remap[right] for right in component_succ[old]]
            if old not in unsat_components:
                remapped_members[new] = sorted(
                    name for name in components[old]
                    if name not in (TOP, BOTTOM) and name not in unsat
                )
        del component_succ, component_pred, components, indegree

        reach = [0] * len(remapped_succ)
        for current, rights in enumerate(remapped_succ):
            bits = 0
            for right in rights:
                if right >= current:
                    raise RuntimeError("component order does not place supers first")
                bits |= (1 << right) | reach[right]
            reach[current] = bits
        name_component = {
            name: component_id
            for component_id, members in enumerate(remapped_members)
            for name in members
        }
        sorted_names = sorted(name_component)
    else:
        remapped_members = []
        reach = []
        name_component = {}
        sorted_names = []

    args.output_prefix.parent.mkdir(parents=True, exist_ok=True)
    node_path = Path(str(args.output_prefix) + ".nodes.tsv.gz")
    unsat_path = Path(str(args.output_prefix) + ".unsat.txt.gz")
    taxonomy_digest = hashlib.sha256()
    taxonomy_digest.update(b"consistent\x01" if consistent else b"consistent\x00")
    pair_count = 0
    nonempty_lefts = 0
    with gzip.open(node_path, "wt", encoding="utf-8") as node_handle:
        if consistent:
            for left in sorted_names:
                component_id = name_component[left]
                rights = [name for name in remapped_members[component_id] if name != left]
                bits = reach[component_id]
                while bits:
                    least = bits & -bits
                    rights.extend(remapped_members[least.bit_length() - 1])
                    bits ^= least
                if not rights:
                    continue
                rights.sort()
                left_digest = hashlib.sha256()
                for right in rights:
                    frame(left_digest, right)
                right_hash = left_digest.hexdigest()
                node_handle.write(f"{left}\t{len(rights)}\t{right_hash}\n")
                taxonomy_digest.update(b"P")
                frame(taxonomy_digest, left)
                taxonomy_digest.update(len(rights).to_bytes(8, "big"))
                taxonomy_digest.update(bytes.fromhex(right_hash))
                pair_count += len(rights)
                nonempty_lefts += 1

    with gzip.open(unsat_path, "wt", encoding="utf-8") as unsat_handle:
        taxonomy_digest.update(b"U")
        for name in sorted(unsat):
            unsat_handle.write(name + "\n")
            frame(taxonomy_digest, name)

    record = {
        "schema_version": 1,
        "algorithm": "full-iri-scc-component-bitset-fingerprint-v1",
        "status": "ok",
        "consistent": bool(consistent),
        "subsumptions": pair_count,
        "unsatisfiable": len(unsat),
        "nonempty_lefts": nonempty_lefts,
        "components": len(reach),
        "source_edges": source_edges,
        "source_equivalence_groups": source_groups,
        "source_declarations": source_declared,
        "ontology_declarations": len(ontology_declared),
        "source_ontology": str(args.source_ontology) if args.source_ontology else None,
        "source_ontology_sha256": (
            sha256_file(args.source_ontology) if args.source_ontology else None
        ),
        "input": str(args.input),
        "input_sha256": sha256_file(args.input),
        "format": args.format,
        "taxonomy_sha256": taxonomy_digest.hexdigest(),
        "node_fingerprints": str(node_path),
        "node_fingerprints_sha256": sha256_file(node_path),
        "unsatisfiable_names": str(unsat_path),
        "unsatisfiable_names_sha256": sha256_file(unsat_path),
        "wall_s": round(time.monotonic() - started, 4),
        "peak_mb": round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024, 2),
    }
    result_path = Path(str(args.output_prefix) + ".json")
    result_tmp = Path(str(result_path) + ".tmp")
    result_tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    result_tmp.replace(result_path)
    print(json.dumps(record, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

