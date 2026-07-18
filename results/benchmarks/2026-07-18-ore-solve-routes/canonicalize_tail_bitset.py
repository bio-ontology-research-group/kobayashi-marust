#!/usr/bin/env python3
"""Memory-bounded exact ORE canonicalization using component bitsets.

The standard canonicalizer stores a Python set for every component's reachable
components. On the 123k-class 3524/15703 taxonomy that representation exceeds
20 GiB. This implementation computes the same SCC-condensed reachability with
Python integer bitsets, then streams sorted signature pairs to gzip.
"""

from __future__ import annotations

import argparse
from collections import deque
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import time


TOP = "owl:Thing"
BOTTOM = "owl:Nothing"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_module(path: Path):
    spec = importlib.util.spec_from_file_location("ore_canon_bitset_source", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load canonicalizer: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--canonicalizer", type=Path, required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--format", choices=("json", "functional", "owlxml"), required=True)
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    started = time.monotonic()
    module = load_module(args.canonicalizer)
    text = args.input.read_text(encoding="utf-8", errors="replace")
    consistent, edges, groups, input_unsat, declared = module.PARSERS[args.format](text)
    del text

    def norm(name: str) -> str:
        if module._is_thing(name):
            return TOP
        if module._is_nothing(name):
            return BOTTOM
        return name

    if not consistent:
        edges = []
        groups = []
        input_unsat = set()
        declared = set()

    succ: dict[str, set[str]] = {}
    nodes: set[str] = set()

    def add(left: str, right: str) -> None:
        left = norm(left)
        right = norm(right)
        nodes.add(left)
        nodes.add(right)
        if left != right:
            succ.setdefault(left, set()).add(right)

    for left, right in edges:
        add(left, right)
    del edges
    for group in groups:
        names = [norm(name) for name in group]
        nodes.update(names)
        representative = names[0]
        for name in names[1:]:
            add(name, representative)
            add(representative, name)
    del groups

    unsat = {norm(name) for name in input_unsat}
    nodes.update(unsat)
    nodes.update(norm(name) for name in declared)
    del input_unsat, declared

    for name in list(nodes):
        if name not in (TOP, BOTTOM):
            add(name, TOP)

    if not consistent:
        nodes.clear()
        succ.clear()

    if nodes:
        component, components = module._sccs(nodes, succ)
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

    bottom_components = {
        component[name]
        for name in component
        if module._is_nothing(name)
    }
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
        unsat.update(
            name for name in components[component_id]
            if not module._is_nothing(name)
        )

    if consistent:
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
        for new, old in enumerate(general_to_specific):
            remapped_succ[new] = [remap[right] for right in component_succ[old]]
            if old not in unsat_components:
                remapped_members[new] = sorted(
                    name for name in components[old]
                    if not module._is_thing(name)
                    and not module._is_nothing(name)
                    and name not in unsat
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

    args.output.parent.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256()
    pair_count = 0

    def emit(handle, line: str) -> None:
        digest.update(line.encode("utf-8"))
        handle.write(line)

    with gzip.open(args.output, "wt", encoding="utf-8") as handle:
        emit(handle, "1\n" if consistent else "0\n")
        if consistent:
            for left in sorted_names:
                component_id = name_component[left]
                rights = [
                    name for name in remapped_members[component_id]
                    if name != left
                ]
                bits = reach[component_id]
                while bits:
                    least = bits & -bits
                    right_component = least.bit_length() - 1
                    rights.extend(remapped_members[right_component])
                    bits ^= least
                for right in sorted(rights):
                    emit(handle, f"{left}\t{right}\n")
                    pair_count += 1
        emit(handle, "#UNSAT\n")
        for name in sorted(unsat):
            emit(handle, f"{name}\n")

    record = {
        "schema_version": 1,
        "algorithm": "scc-component-python-int-bitset-v1",
        "status": "ok",
        "consistent": bool(consistent),
        "subsumptions": pair_count,
        "unsatisfiable": len(unsat),
        "components": len(reach),
        "input": str(args.input),
        "input_sha256": sha256_file(args.input),
        "canonicalizer": str(args.canonicalizer),
        "canonicalizer_sha256": sha256_file(args.canonicalizer),
        "format": args.format,
        "signature": str(args.output),
        "signature_sha256": digest.hexdigest(),
        "signature_gzip_sha256": sha256_file(args.output),
        "signature_bytes": args.output.stat().st_size,
        "wall_s": round(time.monotonic() - started, 4),
        "peak_mb": round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024, 2),
    }
    result_path = args.output.with_suffix(args.output.suffix + ".json")
    result_tmp = result_path.with_suffix(result_path.suffix + ".tmp")
    result_tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    result_tmp.replace(result_path)
    print(json.dumps(record, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
