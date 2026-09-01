#!/usr/bin/env python3
"""Verify the source-level disagreement derivations used in the paper.

This is deliberately a small proof-certificate checker, not an OWL reasoner.
It checks that the hash-bound explanation contains each stated premise and
then applies a deliberately small set of standard DL inferences named in each
report.  It is not a replacement general-purpose reasoner.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from pathlib import Path


DOID = "http://purl.obolibrary.org/obo/DOID_"
CVDO = "http://purl.obolibrary.org/obo/CVDO_"
OBO = "http://purl.obolibrary.org/obo/"
KISAO = "http://www.biomodels.net/kisao/KISAO#KISAO_"


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            value.update(chunk)
    return value.hexdigest()


def compact(value: str) -> str:
    return re.sub(r"\s+", " ", value.strip())


def axioms(path: Path) -> set[str]:
    rows = path.read_text(encoding="utf-8").splitlines()
    if not rows or rows[-1] != "Z\tcomplete":
        raise ValueError(f"incomplete explanation: {path}")
    return {compact(row[2:]) for row in rows if row.startswith("A\t")}


def iri(value: str) -> str:
    return f"<{value}>"


def cls(prefix: str, suffix: str) -> str:
    return iri(prefix + suffix)


def sub(left: str, right: str) -> str:
    return f"SubClassOf({left} {right})"


def some(role: str, filler: str) -> str:
    return f"ObjectSomeValuesFrom({role} {filler})"


def intersection(*values: str) -> str:
    return f"ObjectIntersectionOf({' '.join(values)})"


def union(*values: str) -> str:
    return f"ObjectUnionOf({' '.join(values)})"


def equiv(left: str, right: str) -> str:
    # OWLAPI's renderer leaves one space before the final parenthesis.
    return f"EquivalentClasses({left} {right} )"


def data_has(role: str, lexical: str, datatype: str) -> str:
    return f'DataHasValue({role} "{lexical}"^^{datatype})'


def require(premises: set[str], *wanted: str) -> None:
    missing = [value for value in wanted if compact(value) not in premises]
    if missing:
        raise ValueError("missing witness premises:\n" + "\n".join(missing))


def verify_doid(path: Path) -> dict:
    p = axioms(path)
    disease = cls(DOID, "4")
    source = cls(DOID, "1024")
    target = cls(DOID, "7")
    role = iri(OBO + "RO_0004026")
    fillers = [cls(OBO, value) for value in (
        "UBERON_0000473", "UBERON_0000970", "UBERON_0000010", "UBERON_0001557"
    )]
    branch_classes = [cls(DOID, value) for value in ("2519", "5614", "574", "974")]
    branch_paths = [
        ["2519", "2277", "28", "7"],
        ["5614", "0050155", "863", "7"],
        ["574", "863", "7"],
        ["974", "1579", "7"],
    ]
    named_path = ["1024", "0050338", "104", "0050117"]
    virus_union = union(*(cls(OBO, value) for value in (
        "NCBITaxon_10239", "NCBITaxon_2", "NCBITaxon_2759", "NCBITaxon_36469"
    )))
    require(p, *(sub(cls(DOID, a), cls(DOID, b))
                 for a, b in zip(named_path, named_path[1:])))
    require(p, equiv(cls(DOID, "0050117"),
                     intersection(disease, some(iri(OBO + "IDO_0000664"), virus_union))))
    source_union = [cls(OBO, value) for value in (
        "UBERON_0000010", "UBERON_0000473", "UBERON_0000970", "UBERON_0001557"
    )]
    require(p, sub(source, some(role, union(*source_union))))
    for branch, filler, path_values in zip(branch_classes, fillers, branch_paths):
        require(p, equiv(branch, intersection(disease, some(role, filler))))
        require(p, *(sub(cls(DOID, a), cls(DOID, b))
                     for a, b in zip(path_values, path_values[1:])))

    return {
        "ontology": "doid", "status": "entailed", "query": [source, target],
        "premise_count": len(p),
        "derivation": [
            "named-class transitivity gives DOID_1024 <= DOID_0050117",
            "equivalence projection gives DOID_0050117 <= DOID_4",
            "the asserted existential has a filler in one of four union branches",
            "in each branch, conjunction introduction and equivalence give its defined disease class",
            "each of the four defined classes reaches DOID_7 by the checked named hierarchy",
            "finite case analysis therefore gives DOID_1024 <= DOID_7",
        ],
        "case_branches": len(fillers), "rules": [
            "subsumption transitivity", "equivalence projection", "conjunction introduction",
            "existential-union case analysis",
        ],
    }


def verify_cvdo(path: Path) -> dict:
    p = axioms(path)
    source = cls(CVDO, "0000010")
    target = cls(CVDO, "0000546")
    d60000 = cls(DOID, "0060000")
    ogms31 = cls(OBO, "OGMS_0000031")
    ogms63 = cls(OBO, "OGMS_0000063")
    c405 = cls(CVDO, "0000405")
    c403 = cls(CVDO, "0000403")
    r = iri(OBO + "BFO_0000054")
    s = iri(OBO + "BFO_0000117")
    fma = cls(OBO, "FMA_7280")
    require(p,
            sub(source, d60000), sub(d60000, ogms31),
            sub(d60000, some(r, intersection(ogms63, some(s, c405)))),
            equiv(c405, intersection(c403, some(iri(OBO + "BFO_0000066"), fma))),
            equiv(target, intersection(ogms31, some(r, intersection(ogms63, some(s, c403))))))
    return {
        "ontology": "cvdo", "status": "entailed", "query": [source, target],
        "premise_count": len(p),
        "derivation": [
            "equivalence projection gives CVDO_0000405 <= CVDO_0000403",
            "existential monotonicity propagates this through BFO_0000117 and BFO_0000054",
            "named-class transitivity gives CVDO_0000010 <= OGMS_0000031",
            "conjunction introduction matches the checked definition of CVDO_0000546",
            "reverse equivalence projection gives CVDO_0000010 <= CVDO_0000546",
        ],
        "rules": ["equivalence projection", "existential monotonicity",
                  "subsumption transitivity", "conjunction introduction"],
    }


def verify_kisao(path: Path) -> dict:
    p = axioms(path)
    source = cls(KISAO, "0000086")
    bottom = iri("http://www.w3.org/2002/07/owl#Nothing")
    c0 = cls(KISAO, "0000000")
    c64 = cls(KISAO, "0000064")
    c97 = cls(KISAO, "0000097")
    c104 = cls(KISAO, "0000104")
    c106 = cls(KISAO, "0000106")
    c201 = cls(KISAO, "0000201")
    c261 = cls(KISAO, "0000261")
    c302 = cls(KISAO, "0000302")
    c435 = cls(KISAO, "0000435")
    r245 = cls(KISAO, "0000245")
    d275 = cls(KISAO, "0000275")
    r360 = cls(KISAO, "0000360")
    r361 = cls(KISAO, "0000361")
    integer = "xsd:integer"
    definition = intersection(
        c302,
        some(r360, intersection(c64, data_has(d275, "4", integer))),
        some(r360, intersection(c64, data_has(d275, "5", integer))),
    )
    require(
        p,
        f"DisjointClasses({c0} {c97} {c201})",
        equiv(c435, definition),
        f"ObjectPropertyDomain({r245} {c0})",
        f"ObjectPropertyRange({r245} {c97})",
        sub(c64, some(r361, c261)),
        sub(source, c435),
        sub(c106, some(r245, c104)),
        sub(c261, some(r245, c106)),
    )
    return {
        "ontology": "kisao", "status": "entailed", "query": [source, bottom],
        "premise_count": len(p),
        "derivation": [
            "the checked existential on KISAO_0000106 and the property domain imply KISAO_0000106 <= KISAO_0000000",
            "the checked existential from KISAO_0000261 and the property range imply its KISAO_0000106 successor is in KISAO_0000097",
            "pairwise disjointness of KISAO_0000000 and KISAO_0000097 makes KISAO_0000106 unsatisfiable",
            "existential propagation makes KISAO_0000261 and then KISAO_0000064 unsatisfiable",
            "the checked KISAO_0000435 definition requires a KISAO_0000064 successor, so KISAO_0000435 is unsatisfiable",
            "the asserted subclass axiom therefore gives KISAO_0000086 <= owl:Nothing",
        ],
        "rules": ["property domain", "property range", "pairwise disjointness",
                  "existential bottom propagation", "equivalence projection",
                  "subsumption transitivity"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ledger", required=True, type=Path)
    parser.add_argument("--evidence-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    with args.ledger.open(encoding="utf-8", newline="") as stream:
        ledger = {row["ontology"]: row for row in csv.DictReader(stream, delimiter="\t")}
    reports = []
    for name, checker in (("doid", verify_doid), ("cvdo", verify_cvdo),
                          ("kisao", verify_kisao)):
        path = args.evidence_root / name / "explanation.tsv"
        module = args.evidence_root / name / "module.ofn"
        if digest(path) != ledger[name]["explanation_sha256"]:
            raise ValueError(f"explanation digest mismatch: {name}")
        if digest(module) != ledger[name]["module_sha256"]:
            raise ValueError(f"module digest mismatch: {name}")
        report = checker(path)
        if report["premise_count"] != int(ledger[name]["explanation_axioms"]):
            raise ValueError(f"premise count mismatch: {name}")
        report["source_sha256"] = ledger[name]["source_sha256"]
        report["module_sha256"] = digest(module)
        report["explanation_sha256"] = digest(path)
        reports.append(report)
    output = {"schema": 1, "method": "source-level finite derivation certificate", "reports": reports}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("DISAGREEMENT_WITNESSES_OK\t3")


if __name__ == "__main__":
    main()
