#!/usr/bin/env python3
"""Diagnose whether an OFN source misses the direct route only by active disjointness."""

import collections
import pathlib
import re
import sys

path = pathlib.Path(sys.argv[1])
named = re.compile(r"SubClassOf\(<([^>]*)> <([^>]*)>\)$")
complement = re.compile(r"SubClassOf\(<([^>]*)> ObjectComplementOf\(<([^>]*)>\)\)$")
leaf = re.compile(r"SubClassOf\(<([^>]*)> ObjectSomeValuesFrom\(<([^>]*)> <([^>]*)>\)\)$")
declaration = re.compile(r"Declaration\((?:Class|ObjectProperty)\(<[^>]*>\)\)$")
unary_role = re.compile(r"(?:Transitive|Symmetric)ObjectProperty\(<[^>]*>\)$")
binary_role = re.compile(r"(?:SubObjectPropertyOf|InverseObjectProperties|EquivalentObjectProperties)\(<[^>]*> <[^>]*>\)$")

incoming: dict[str, list[str]] = collections.defaultdict(list)
disjoint: list[tuple[str, str]] = []
unsupported: list[tuple[int, str]] = []
for number, raw in enumerate(path.open(), 1):
    line = raw.strip()
    if not line or line == ")" or line.startswith("Prefix(") or line.startswith("Ontology("):
        continue
    if match := named.fullmatch(line):
        incoming[match[2]].append(match[1])
    elif match := complement.fullmatch(line):
        disjoint.append((match[1], match[2]))
    elif leaf.fullmatch(line) or declaration.fullmatch(line) or unary_role.fullmatch(line) or binary_role.fullmatch(line):
        pass
    elif "owl:Thing" in line or "owl:Nothing" in line:
        unsupported.append((number, line))
    else:
        unsupported.append((number, line))

def ancestors(target: str) -> set[str]:
    found: set[str] = set()
    stack = [target]
    while stack:
        current = stack.pop()
        if current in found:
            continue
        found.add(current)
        stack.extend(incoming[current])
    return found

clashing: set[str] = set()
active_pairs = 0
for left, right in disjoint:
    common = ancestors(left) & ancestors(right)
    if common:
        active_pairs += 1
        clashing.update(common)

print(f"unsupported={len(unsupported)} disjoint={len(disjoint)} active_pairs={active_pairs} clashing_sources={len(clashing)}")
for item in unsupported[:20]:
    print("UNSUPPORTED", item[0], item[1])
for iri in sorted(clashing)[:20]:
    print("CLASH", iri)
