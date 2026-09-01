#!/usr/bin/env python3
"""SCC/closure fingerprint for large JSON or OWL/XML taxonomy outputs."""

from __future__ import annotations

import argparse
from array import array
from collections import deque
import gzip
import hashlib
import json
from pathlib import Path
import resource
import time
import xml.etree.ElementTree as ET

from fingerprint_km_json_stream import (
    BOTTOM, TOP, clean_iri, frame, scan, sha256_file, source_declarations,
)


NONE = 0xFFFFFFFF


def local_name(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def scan_owlxml(path: Path, visit_pair, visit_equivalence_pair,
                visit_declaration) -> int:
    """Stream top-level taxonomy axioms without retaining the XML tree."""
    context = ET.iterparse(path, events=("start", "end"))
    event, root = next(context)
    if event != "start" or local_name(root.tag) != "Ontology":
        raise ValueError("OWL/XML taxonomy has no Ontology root")
    depth = 0
    equivalence_groups = 0
    for event, element in context:
        if event == "start":
            depth += 1
            continue
        if depth == 1:
            kind = local_name(element.tag)
            classes = [clean_iri(child.attrib["IRI"])
                       for child in element if local_name(child.tag) == "Class"
                       and "IRI" in child.attrib]
            if kind == "Declaration" and len(classes) == 1:
                visit_declaration(classes[0])
            elif kind == "SubClassOf" and len(classes) == 2:
                visit_pair(classes[0], classes[1])
            elif kind == "EquivalentClasses" and len(classes) >= 2:
                equivalence_groups += 1
                representative = classes[0]
                for name in classes[1:]:
                    visit_equivalence_pair(representative, name)
                    visit_equivalence_pair(name, representative)
            root.clear()
        depth -= 1
    return equivalence_groups


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--format", choices=("json", "owlxml"), default="json")
    parser.add_argument("--source-ontology", type=Path)
    parser.add_argument("--output-prefix", required=True, type=Path)
    parser.add_argument("--pairs-output", type=Path,
                        help="optionally emit the sorted closed S/sub/super relation")
    args = parser.parse_args()
    started = time.monotonic()

    name_id: dict[str, int] = {}
    names: list[str] = []
    pair_lefts = array("I")
    pair_rights = array("I")
    source_edges = 0
    previous_pair: tuple[str, str] | None = None
    explicit_unsat_names: set[str] = set()
    declared_flags = bytearray()

    def intern(name: str) -> int:
        found = name_id.get(name)
        if found is not None:
            return found
        found = len(names)
        name_id[name] = found
        names.append(name)
        declared_flags.append(0)
        return found

    def declare(name: str) -> None:
        declared_flags[intern(name)] = 1

    def add_pair(left: str, right: str, *, count_source: bool = True) -> None:
        nonlocal source_edges, previous_pair
        pair = (left, right)
        if args.format == "json" and previous_pair is not None and pair <= previous_pair:
            raise ValueError("KM subsumptions are not sorted and unique")
        previous_pair = pair
        if count_source:
            source_edges += 1
        left_id, right_id = intern(left), intern(right)
        if left_id != right_id:
            pair_lefts.append(left_id)
            pair_rights.append(right_id)

    if args.format == "json":
        consistent = scan(args.input, add_pair, explicit_unsat_names.add)
        source_groups = 0
    else:
        consistent = True
        source_groups = scan_owlxml(
            args.input, add_pair,
            lambda left, right: add_pair(left, right, count_source=False),
            declare,
        )
    unsat_ids = {intern(name) for name in explicit_unsat_names}
    del explicit_unsat_names

    declarations = source_declarations(args.source_ontology)
    if consistent:
        # The reference fingerprinter includes every source declaration in the
        # graph and gives every named class the implicit owl:Thing superclass.
        # These edges disappear from the published relation, but they matter
        # for isolated declarations and inconsistency propagation.
        for name in declarations:
            intern(name)
        original_node_count = len(names)
        top_id = intern(TOP)
        for node in range(original_node_count):
            if node != top_id and names[node] != BOTTOM:
                pair_lefts.append(node)
                pair_rights.append(top_id)

    node_count = len(names)
    lengths = array("I", [0]) * node_count
    for left in pair_lefts:
        lengths[left] += 1
    starts = array("Q", [0]) * node_count
    total = 0
    for node, count in enumerate(lengths):
        starts[node] = total
        total += count
    cursor = array("Q", starts)
    edges = array("I", [0]) * total
    for left, right in zip(pair_lefts, pair_rights):
        position = cursor[left]
        edges[position] = right
        cursor[left] += 1
    del pair_lefts, pair_rights, cursor

    taxonomy_digest = hashlib.sha256()
    relation_digest = hashlib.sha256()
    node_path = Path(str(args.output_prefix) + ".nodes.tsv.gz")
    unsat_path = Path(str(args.output_prefix) + ".unsat.txt.gz")
    args.output_prefix.parent.mkdir(parents=True, exist_ok=True)
    if args.pairs_output is not None:
        args.pairs_output.parent.mkdir(parents=True, exist_ok=True)

    if not consistent:
        taxonomy_digest.update(b"consistent\x00")
        taxonomy_digest.update(b"U")
        relation_digest.update(b"U")
        with gzip.open(node_path, "wt", encoding="utf-8"):
            pass
        with gzip.open(unsat_path, "wt", encoding="utf-8"):
            pass
        if args.pairs_output is not None:
            args.pairs_output.write_text("", encoding="utf-8")
        component_count = 0
        pair_count = nonempty_lefts = 0
        unsat_names: list[str] = []
    else:
        unseen = -1
        index = array("i", [unseen]) * node_count
        low = array("I", [0]) * node_count
        on_stack = bytearray(node_count)
        component = array("I", [NONE]) * node_count
        tarjan_stack = array("I")
        counter = 0
        component_count = 0

        def edge_bounds(node: int) -> tuple[int, int]:
            start = starts[node]
            return start, start + lengths[node]

        # Frames are [node, next edge, end edge]. Graph depth is normally small;
        # edge and node bulk remains in compact arrays.
        for root in range(node_count):
            if index[root] != unseen:
                continue
            index[root] = low[root] = counter
            counter += 1
            tarjan_stack.append(root)
            on_stack[root] = 1
            begin, end = edge_bounds(root)
            frames: list[list[int]] = [[root, begin, end]]
            while frames:
                node, position, edge_end = frames[-1]
                if position < edge_end:
                    target = edges[position]
                    frames[-1][1] += 1
                    if index[target] == unseen:
                        index[target] = low[target] = counter
                        counter += 1
                        tarjan_stack.append(target)
                        on_stack[target] = 1
                        child_begin, child_end = edge_bounds(target)
                        frames.append([target, child_begin, child_end])
                    elif on_stack[target]:
                        low[node] = min(low[node], index[target])
                    continue
                if low[node] == index[node]:
                    while True:
                        member = tarjan_stack.pop()
                        on_stack[member] = 0
                        component[member] = component_count
                        if member == node:
                            break
                    component_count += 1
                frames.pop()
                if frames:
                    parent = frames[-1][0]
                    low[parent] = min(low[parent], low[node])
        del index, low, on_stack, tarjan_stack

        member_counts = array("I", [0]) * component_count
        for value in component:
            member_counts[value] += 1
        member_offsets = array("Q", [0]) * (component_count + 1)
        for position, count in enumerate(member_counts):
            member_offsets[position + 1] = member_offsets[position] + count
        member_cursor = array("Q", member_offsets[:-1])
        members = array("I", [0]) * node_count
        for node, component_id in enumerate(component):
            position = member_cursor[component_id]
            members[position] = node
            member_cursor[component_id] += 1
        del member_cursor, member_counts

        component_starts = array("Q", [0]) * component_count
        component_lengths = array("I", [0]) * component_count
        component_edges = array("I")
        for component_id in range(component_count):
            outgoing: set[int] = set()
            for member_position in range(member_offsets[component_id], member_offsets[component_id + 1]):
                node = members[member_position]
                begin, end = edge_bounds(node)
                for edge_position in range(begin, end):
                    target_component = component[edges[edge_position]]
                    if target_component != component_id:
                        outgoing.add(target_component)
            component_starts[component_id] = len(component_edges)
            ordered = sorted(outgoing)
            component_lengths[component_id] = len(ordered)
            component_edges.extend(ordered)

        reverse_counts = array("I", [0]) * component_count
        indegree = array("I", [0]) * component_count
        for target in component_edges:
            reverse_counts[target] += 1
            indegree[target] += 1
        reverse_offsets = array("Q", [0]) * (component_count + 1)
        for position, count in enumerate(reverse_counts):
            reverse_offsets[position + 1] = reverse_offsets[position] + count
        reverse_cursor = array("Q", reverse_offsets[:-1])
        reverse_edges = array("I", [0]) * len(component_edges)
        for source in range(component_count):
            begin = component_starts[source]
            for position in range(begin, begin + component_lengths[source]):
                target = component_edges[position]
                slot = reverse_cursor[target]
                reverse_edges[slot] = source
                reverse_cursor[target] += 1
        del reverse_counts, reverse_cursor

        unsat_components = {component[node] for node in unsat_ids}
        bottom_id = name_id.get(BOTTOM)
        if bottom_id is not None:
            unsat_components.add(component[bottom_id])
        pending = list(unsat_components)
        while pending:
            target = pending.pop()
            for position in range(reverse_offsets[target], reverse_offsets[target + 1]):
                predecessor = reverse_edges[position]
                if predecessor not in unsat_components:
                    unsat_components.add(predecessor)
                    pending.append(predecessor)
        top_id = name_id.get(TOP)
        if top_id is not None and component[top_id] in unsat_components:
            consistent = False

        unsat_names = sorted(
            names[node]
            for component_id in unsat_components
            for node in members[member_offsets[component_id]:member_offsets[component_id + 1]]
            if names[node] != BOTTOM
        )

        if not consistent:
            taxonomy_digest.update(b"consistent\x00")
            taxonomy_digest.update(b"U")
            relation_digest.update(b"U")
            with gzip.open(node_path, "wt", encoding="utf-8"):
                pass
            with gzip.open(unsat_path, "wt", encoding="utf-8") as handle:
                for name in unsat_names:
                    handle.write(name + "\n")
                    frame(taxonomy_digest, name)
                    frame(relation_digest, name)
            pair_count = nonempty_lefts = 0
            component_count = 0
        else:
            ready = deque(i for i, degree in enumerate(indegree) if degree == 0)
            specific_to_general = array("I")
            while ready:
                current = ready.popleft()
                specific_to_general.append(current)
                begin = component_starts[current]
                for position in range(begin, begin + component_lengths[current]):
                    target = component_edges[position]
                    indegree[target] -= 1
                    if indegree[target] == 0:
                        ready.append(target)
            if len(specific_to_general) != component_count:
                raise RuntimeError("SCC condensation unexpectedly contains a cycle")

            reach: list[array | None] = [None] * component_count
            for current in reversed(specific_to_general):
                closure: set[int] = set()
                begin = component_starts[current]
                for position in range(begin, begin + component_lengths[current]):
                    target = component_edges[position]
                    closure.add(target)
                    inherited = reach[target]
                    if inherited is not None:
                        closure.update(inherited)
                if closure:
                    reach[current] = array("I", sorted(closure))

            excluded_names = {TOP, BOTTOM}
            unsat_name_set = set(unsat_names)
            sorted_nodes = sorted(
                (node for node, name in enumerate(names)
                 if name not in excluded_names and name not in unsat_name_set),
                key=names.__getitem__,
            )
            taxonomy_digest.update(b"consistent\x01")
            pair_count = nonempty_lefts = 0
            pair_handle = (args.pairs_output.open("w", encoding="utf-8")
                           if args.pairs_output is not None else None)
            try:
                with gzip.open(node_path, "wt", encoding="utf-8") as node_handle:
                    for left_node in sorted_nodes:
                        component_id = component[left_node]
                        right_nodes: list[int] = []
                        for position in range(member_offsets[component_id], member_offsets[component_id + 1]):
                            node = members[position]
                            if node != left_node and names[node] not in excluded_names and names[node] not in unsat_name_set:
                                right_nodes.append(node)
                        inherited = reach[component_id]
                        if inherited is not None:
                            for right_component in inherited:
                                if right_component in unsat_components:
                                    continue
                                for position in range(member_offsets[right_component], member_offsets[right_component + 1]):
                                    node = members[position]
                                    if names[node] not in excluded_names and names[node] not in unsat_name_set:
                                        right_nodes.append(node)
                        if not right_nodes:
                            continue
                        right_nodes.sort(key=names.__getitem__)
                        right_digest = hashlib.sha256()
                        for node in right_nodes:
                            frame(right_digest, names[node])
                        packed = right_digest.digest()
                        left = names[left_node]
                        node_handle.write(f"{left}\t{len(right_nodes)}\t{right_digest.hexdigest()}\n")
                        for digest in (taxonomy_digest, relation_digest):
                            digest.update(b"P")
                            frame(digest, left)
                            digest.update(len(right_nodes).to_bytes(8, "big"))
                            digest.update(packed)
                        if pair_handle is not None:
                            for node in right_nodes:
                                pair_handle.write(f"S\t{left}\t{names[node]}\n")
                        pair_count += len(right_nodes)
                        nonempty_lefts += 1
            finally:
                if pair_handle is not None:
                    pair_handle.close()
            taxonomy_digest.update(b"U")
            relation_digest.update(b"U")
            with gzip.open(unsat_path, "wt", encoding="utf-8") as handle:
                for name in unsat_names:
                    handle.write(name + "\n")
                    frame(taxonomy_digest, name)
                    frame(relation_digest, name)

    output_declarations = sum(declared_flags) if args.format == "owlxml" else 0
    missing_declarations = sum(
        1 for name in declarations
        if name not in name_id or not declared_flags[name_id[name]]
    ) if args.format == "owlxml" else len(declarations)
    record = {
        "schema_version": 1,
        "algorithm": ("km-json-sparse-scc-closure-fingerprint-v1"
                      if args.format == "json"
                      else "owlxml-sparse-scc-closure-fingerprint-v1"),
        "status": "ok",
        "consistent": bool(consistent),
        "subsumptions": pair_count,
        "unsatisfiable": len(unsat_names),
        "nonempty_lefts": nonempty_lefts,
        "components": component_count,
        "source_edges": source_edges,
        "source_equivalence_groups": source_groups,
        "source_declarations": output_declarations,
        "output_declarations": output_declarations,
        "ontology_declarations": len(declarations),
        "missing_source_declarations": missing_declarations,
        "source_ontology": str(args.source_ontology) if args.source_ontology else None,
        "source_ontology_sha256": sha256_file(args.source_ontology) if args.source_ontology else None,
        "input": str(args.input),
        "input_sha256": sha256_file(args.input),
        "format": args.format,
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
