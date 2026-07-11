#!/usr/bin/env python3
"""Reduce the 5087 <= 4121 entailment to a small Functional Syntax core."""

from __future__ import annotations

import os
import subprocess
import sys
import xml.etree.ElementTree as ET
from collections import defaultdict, deque
from pathlib import Path


SUB = "UBERON_0005087"
SUP = "UBERON_0004121"
OWL = "{http://www.w3.org/2002/07/owl#}"
LOGICAL_PREFIXES = (
    "AsymmetricObjectProperty(",
    "DataPropertyDomain(",
    "DataPropertyRange(",
    "DisjointClasses(",
    "DisjointObjectProperties(",
    "EquivalentClasses(",
    "EquivalentObjectProperties(",
    "FunctionalObjectProperty(",
    "InverseFunctionalObjectProperty(",
    "InverseObjectProperties(",
    "IrreflexiveObjectProperty(",
    "ObjectPropertyDomain(",
    "ObjectPropertyRange(",
    "ReflexiveObjectProperty(",
    "SubClassOf(",
    "SubObjectPropertyOf(",
    "SymmetricObjectProperty(",
    "TransitiveObjectProperty(",
)


def local(iri: str) -> str:
    return iri.rsplit("/", 1)[-1].rsplit("#", 1)[-1]


def entailed(taxonomy: Path) -> bool:
    graph: dict[str, list[str]] = defaultdict(list)
    for axiom in ET.parse(taxonomy).getroot():
        kind = axiom.tag.rsplit("}", 1)[-1]
        classes = [
            local(child.attrib["IRI"])
            for child in axiom
            if child.tag == OWL + "Class" and "IRI" in child.attrib
        ]
        if kind == "SubClassOf" and len(classes) == 2:
            graph[classes[0]].append(classes[1])
        elif kind == "EquivalentClasses":
            for left in classes:
                graph[left].extend(right for right in classes if right != left)
    queue = deque([SUB])
    seen = {SUB}
    while queue:
        node = queue.popleft()
        if node == SUP:
            return True
        for parent in graph[node]:
            if parent not in seen:
                seen.add(parent)
                queue.append(parent)
    return False


def main() -> int:
    if len(sys.argv) != 4:
        print(f"usage: {sys.argv[0]} INPUT.ofn KONCLUDE OUTPUT.ofn", file=sys.stderr)
        return 2
    source, konclude, output = map(Path, sys.argv[1:])
    lines = source.read_text().splitlines()
    prefixes = [line for line in lines if line.startswith("Prefix(")]
    declarations = [line for line in lines if line.startswith("Declaration(")]
    candidates = [line for line in lines if line.startswith(LOGICAL_PREFIXES)]
    work = output.with_suffix(".work.ofn")
    taxonomy = output.with_suffix(".taxonomy.owl")
    attempts = 0

    def test(selected: list[str]) -> bool:
        nonlocal attempts
        attempts += 1
        work.write_text(
            "\n".join([*prefixes, "Ontology(", *declarations, *selected, ")", ""])
        )
        env = os.environ.copy()
        env["LD_LIBRARY_PATH"] = "/tmp" + (
            ":" + env["LD_LIBRARY_PATH"] if env.get("LD_LIBRARY_PATH") else ""
        )
        result = subprocess.run(
            [
                str(konclude),
                "classification",
                "-w",
                "1",
                "-i",
                str(work),
                "-o",
                str(taxonomy),
            ],
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=30,
            check=False,
        )
        return result.returncode == 0 and taxonomy.exists() and entailed(taxonomy)

    if not test(candidates):
        print("baseline does not preserve entailment", file=sys.stderr)
        return 1
    granularity = 2
    while len(candidates) >= 2:
        chunk_size = (len(candidates) + granularity - 1) // granularity
        reduced = False
        for start in range(0, len(candidates), chunk_size):
            trial = candidates[:start] + candidates[start + chunk_size :]
            if trial and test(trial):
                candidates = trial
                granularity = max(2, granularity - 1)
                reduced = True
                print(f"attempt={attempts} axioms={len(candidates)}", flush=True)
                break
        if not reduced:
            if granularity >= len(candidates):
                break
            granularity = min(len(candidates), granularity * 2)

    output.write_text(
        "\n".join([*prefixes, "Ontology(", *declarations, *candidates, ")", ""])
    )
    print(f"done attempts={attempts} axioms={len(candidates)} output={output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
