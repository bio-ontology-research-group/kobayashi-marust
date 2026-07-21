#!/usr/bin/env python3
"""Audit datatype influence in the exact saved ORE 10621 TInput.

This script is deliberately reasoner-free.  It inventories every generated
datatype symbol, every source axiom and normalized clause that mentions one,
and an undirected concept/role hypergraph closure seeded by those symbols.  The
closure is an over-approximation used to scope a sound bridge mechanism; it is
not a semantic certificate and cannot establish a solve claim.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_sha256(value: object) -> str:
    payload = json.dumps(
        value, ensure_ascii=False, separators=(",", ":"), sort_keys=True
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def one_variant(value: Any) -> tuple[str, Any]:
    if isinstance(value, str):
        return value, None
    if not isinstance(value, dict) or len(value) != 1:
        raise ValueError(f"expected one externally tagged variant, got {value!r}")
    return next(iter(value.items()))


def role_symbols(value: Any) -> tuple[set[str], str]:
    variant, payload = one_variant(value)
    if variant == "Name":
        if not isinstance(payload, str):
            raise ValueError(f"invalid named role: {value!r}")
        return {payload}, "Name"
    if variant == "Inverse":
        if not isinstance(payload, str):
            raise ValueError(f"invalid inverse role: {value!r}")
        return {payload}, "Inverse"
    if variant == "Universal":
        return {"__SOURCE_UNIVERSAL_ROLE__"}, "Universal"
    raise ValueError(f"unknown role variant {variant!r}")


def concept_symbols(value: Any) -> tuple[set[str], set[str], str]:
    variant, payload = one_variant(value)
    if variant == "Name":
        if not isinstance(payload, str):
            raise ValueError(f"invalid named concept: {value!r}")
        return {payload}, set(), "Name"
    if variant in {"Top", "Bottom"}:
        return set(), set(), variant
    if variant == "Nominal":
        if not isinstance(payload, str):
            raise ValueError(f"invalid nominal: {value!r}")
        return {f"__nominal_value__{payload}"}, set(), "Nominal"
    if variant == "Not":
        concepts, roles, shape = concept_symbols(payload)
        return concepts, roles, f"Not({shape})"
    if variant in {"And", "Or"}:
        if not isinstance(payload, list):
            raise ValueError(f"invalid {variant} payload: {value!r}")
        concepts: set[str] = set()
        roles: set[str] = set()
        shapes = []
        for operand in payload:
            operand_concepts, operand_roles, operand_shape = concept_symbols(operand)
            concepts.update(operand_concepts)
            roles.update(operand_roles)
            shapes.append(operand_shape)
        return concepts, roles, f"{variant}({','.join(shapes)})"
    if variant in {"Exists", "Forall"}:
        if not isinstance(payload, list) or len(payload) != 2:
            raise ValueError(f"invalid {variant} payload: {value!r}")
        roles, role_shape = role_symbols(payload[0])
        concepts, nested_roles, filler_shape = concept_symbols(payload[1])
        roles.update(nested_roles)
        return concepts, roles, f"{variant}({role_shape},{filler_shape})"
    if variant in {"AtLeast", "AtMost"}:
        if not isinstance(payload, list) or len(payload) != 3:
            raise ValueError(f"invalid {variant} payload: {value!r}")
        cardinality = payload[0]
        roles, role_shape = role_symbols(payload[1])
        concepts, nested_roles, filler_shape = concept_symbols(payload[2])
        roles.update(nested_roles)
        return (
            concepts,
            roles,
            f"{variant}({cardinality},{role_shape},{filler_shape})",
        )
    if variant == "HasSelf":
        roles, role_shape = role_symbols(payload)
        return set(), roles, f"HasSelf({role_shape})"
    raise ValueError(f"unknown concept variant {variant!r}")


class UnionFind:
    def __init__(self) -> None:
        self.parent: dict[str, str] = {}
        self.rank: dict[str, int] = {}

    def add(self, value: str) -> None:
        if value not in self.parent:
            self.parent[value] = value
            self.rank[value] = 0

    def find(self, value: str) -> str:
        self.add(value)
        parent = self.parent[value]
        if parent != value:
            self.parent[value] = self.find(parent)
        return self.parent[value]

    def union_all(self, values: Iterable[str]) -> None:
        ordered = sorted(set(values))
        if not ordered:
            return
        root = self.find(ordered[0])
        for value in ordered[1:]:
            other = self.find(value)
            root = self.find(root)
            if root == other:
                continue
            if self.rank[root] < self.rank[other]:
                root, other = other, root
            self.parent[other] = root
            if self.rank[root] == self.rank[other]:
                self.rank[root] += 1


def atom_symbols(
    atom: dict[str, Any], concepts: list[str], roles: list[str]
) -> tuple[set[str], set[str], str]:
    kind = atom.get("k")
    concept_names: set[str] = set()
    role_names: set[str] = set()
    if kind == "c":
        concept_names.add(concepts[int(atom["c"])])
    elif kind == "e":
        concept_names.add(concepts[int(atom["c"])])
        role_names.add(roles[int(atom["r"])])
    elif kind == "r":
        role_names.add(roles[int(atom["r"])])
    elif kind != "eq":
        raise ValueError(f"unknown HAtom kind: {atom!r}")
    return concept_names, role_names, str(kind)


def datatype_category(name: str) -> str:
    if name.startswith("__dt__val__"):
        return "literal-value"
    if name.startswith("__dt__c__"):
        return "complex-range"
    if "opaque" in name:
        return "opaque"
    return "named-range"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tin", type=Path, required=True)
    parser.add_argument("--tin-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    observed_tin_sha256 = sha256_file(args.tin)
    if observed_tin_sha256 != args.tin_sha256:
        raise SystemExit(
            f"TInput hash mismatch: expected {args.tin_sha256}, "
            f"observed {observed_tin_sha256}"
        )
    tin = json.loads(args.tin.read_text(encoding="utf-8"))
    concepts = tin.get("concepts") or []
    roles = tin.get("roles") or []
    clauses = tin.get("clauses") or []
    source_axioms = tin.get("source_axioms") or []
    queries = tin.get("queries") or []
    if len(concepts) != len(set(concepts)) or len(roles) != len(set(roles)):
        raise SystemExit("TInput concept/role names are not unique")

    dt_names = sorted(name for name in concepts if name.startswith("__dt__"))
    dt_set = set(dt_names)
    dt_ids = {index for index, name in enumerate(concepts) if name in dt_set}
    unit_bottom: list[dict[str, object]] = []
    clause_shape_counts: Counter[str] = Counter()
    pure_dt_shape_counts: Counter[str] = Counter()
    dt_clause_records: list[dict[str, object]] = []
    pure_relation_names: set[str] = set()
    uf = UnionFind()

    for index, clause in enumerate(clauses):
        body = clause.get("body") or []
        head = clause.get("head") or []
        atoms = body + head
        clause_concepts: set[str] = set()
        clause_roles: set[str] = set()
        kinds = []
        for atom in atoms:
            atom_concepts, atom_roles, kind = atom_symbols(atom, concepts, roles)
            clause_concepts.update(atom_concepts)
            clause_roles.update(atom_roles)
            kinds.append(kind)
        symbols = {f"C:{name}" for name in clause_concepts}
        symbols.update(f"R:{name}" for name in clause_roles)
        uf.union_all(symbols)

        shape = (
            f"body={','.join(str(atom.get('k')) for atom in body)};"
            f"head={','.join(str(atom.get('k')) for atom in head)}"
        )
        clause_shape_counts[shape] += 1
        touched_dt = sorted(clause_concepts & dt_set)
        touched_non_dt = sorted(clause_concepts - dt_set)
        if touched_dt:
            has_role_or_exist = any(kind in {"r", "e"} for kind in kinds)
            has_eq = "eq" in kinds
            pure_dt = not touched_non_dt and not has_role_or_exist
            category = (
                "pure-dt-concept-eq"
                if pure_dt and has_eq
                else (
                    "pure-dt-concept"
                    if pure_dt
                    else (
                        "dt-with-role-or-exist"
                        if has_role_or_exist
                        else "dt-with-non-dt-concept"
                    )
                )
            )
            if pure_dt:
                pure_relation_names.update(touched_dt)
                pure_dt_shape_counts[shape] += 1
            dt_clause_records.append(
                {
                    "index": index,
                    "category": category,
                    "shape": shape,
                    "datatype_names": touched_dt,
                    "non_datatype_concepts": touched_non_dt,
                    "roles": sorted(clause_roles),
                    "clause_sha256": canonical_sha256(clause),
                }
            )
        if (
            len(body) == 1
            and not head
            and body[0].get("k") == "c"
            and body[0].get("neg") is False
        ):
            concept_id = int(body[0]["c"])
            unit_bottom.append(
                {
                    "clause_index": index,
                    "concept_id": concept_id,
                    "concept": concepts[concept_id],
                    "datatype": concept_id in dt_ids,
                    "clause_sha256": canonical_sha256(clause),
                }
            )

    source_axiom_records: list[dict[str, object]] = []
    source_axiom_kind_counts: Counter[str] = Counter()
    for index, axiom in enumerate(source_axioms):
        left_concepts, left_roles, left_shape = concept_symbols(axiom["left"])
        right_concepts, right_roles, right_shape = concept_symbols(axiom["right"])
        axiom_concepts = left_concepts | right_concepts
        axiom_roles = left_roles | right_roles
        symbols = {f"C:{name}" for name in axiom_concepts}
        symbols.update(f"R:{name}" for name in axiom_roles)
        uf.union_all(symbols)
        touched_dt = sorted(axiom_concepts & dt_set)
        if not touched_dt:
            continue
        kind = str(axiom.get("kind"))
        source_axiom_kind_counts[kind] += 1
        source_axiom_records.append(
            {
                "index": index,
                "kind": kind,
                "left_shape": left_shape,
                "right_shape": right_shape,
                "datatype_names": touched_dt,
                "non_datatype_concepts": sorted(axiom_concepts - dt_set),
                "roles": sorted(axiom_roles),
                "axiom_sha256": canonical_sha256(axiom),
                "left": axiom["left"],
                "right": axiom["right"],
            }
        )

    dt_roots = {uf.find(f"C:{name}") for name in dt_names}
    connected_symbols = sorted(
        symbol for symbol in uf.parent if uf.find(symbol) in dt_roots
    )
    connected_concepts = sorted(
        symbol[2:] for symbol in connected_symbols if symbol.startswith("C:")
    )
    connected_roles = sorted(
        symbol[2:] for symbol in connected_symbols if symbol.startswith("R:")
    )
    query_names = [concepts[int(index)] for index in queries]
    unit_bottom_names = {row["concept"] for row in unit_bottom}
    connected_queries = sorted(set(query_names) & set(connected_concepts))
    connected_queries_not_unit_bottom = sorted(
        set(connected_queries) - unit_bottom_names
    )

    category_counts = Counter(datatype_category(name) for name in dt_names)
    clause_category_counts = Counter(
        str(record["category"]) for record in dt_clause_records
    )
    report = {
        "schema_version": 1,
        "scope": "reasoner-free-exact-tinput-datatype-influence-audit",
        "status": "analyzed",
        "supports_acceptance": False,
        "tinput": str(args.tin),
        "tinput_sha256": observed_tin_sha256,
        "counts": {
            "concepts": len(concepts),
            "roles": len(roles),
            "queries": len(queries),
            "clauses": len(clauses),
            "source_axioms": len(source_axioms),
            "datatype_names": len(dt_names),
            "datatype_source_axioms": len(source_axiom_records),
            "datatype_clauses": len(dt_clause_records),
            "unit_bottom_clauses": len(unit_bottom),
            "datatype_connected_concepts": len(connected_concepts),
            "datatype_connected_roles": len(connected_roles),
            "datatype_connected_queries": len(connected_queries),
            "datatype_connected_queries_not_unit_bottom": len(
                connected_queries_not_unit_bottom
            ),
        },
        "datatype_category_counts": dict(sorted(category_counts.items())),
        "datatype_names": dt_names,
        "opaque_datatype_names": sorted(
            name for name in dt_names if "opaque" in name
        ),
        "complex_datatype_names": sorted(
            name for name in dt_names if name.startswith("__dt__c__")
        ),
        "datatype_names_without_pure_relation_clause": sorted(
            dt_set - pure_relation_names
        ),
        "complex_names_without_pure_relation_clause": sorted(
            name
            for name in dt_set - pure_relation_names
            if name.startswith("__dt__c__")
        ),
        "source_axiom_kind_counts": dict(
            sorted(source_axiom_kind_counts.items())
        ),
        "datatype_clause_category_counts": dict(
            sorted(clause_category_counts.items())
        ),
        "all_clause_shape_counts": dict(sorted(clause_shape_counts.items())),
        "pure_datatype_clause_shape_counts": dict(
            sorted(pure_dt_shape_counts.items())
        ),
        "unit_bottom": unit_bottom,
        "unit_bottom_concepts": sorted(unit_bottom_names),
        "datatype_source_axioms": source_axiom_records,
        "datatype_clauses": dt_clause_records,
        "datatype_connected_concepts": connected_concepts,
        "datatype_connected_roles": connected_roles,
        "datatype_connected_queries": connected_queries,
        "datatype_connected_queries_not_unit_bottom": (
            connected_queries_not_unit_bottom
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(args.output)
    print(json.dumps(report["counts"], sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
