#!/usr/bin/env python3
"""Audit role-local datatype isolation in an exact saved ``TInput``.

This is a structural, reasoner-free audit.  It proves only the premises it
reports: the accepted source-axiom shapes, direct RBox/HT-clause connectivity
between data roles, and absence of object fillers on roles carrying datatype
ranges.  It is not by itself a soundness or completeness certificate.
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


def one_variant(value: Any) -> tuple[str, Any]:
    if isinstance(value, str):
        return value, None
    if not isinstance(value, dict) or len(value) != 1:
        raise ValueError(f"expected one externally tagged variant: {value!r}")
    return next(iter(value.items()))


def role_name(value: Any) -> str:
    variant, payload = one_variant(value)
    if variant in {"Name", "Inverse"} and isinstance(payload, str):
        return payload
    if variant == "Universal":
        return "__SOURCE_UNIVERSAL_ROLE__"
    raise ValueError(f"unsupported source role: {value!r}")


def concept_restrictions(value: Any) -> list[dict[str, str]]:
    variant, payload = one_variant(value)
    if variant in {"Name", "Top", "Bottom", "Nominal"}:
        return []
    if variant == "Not":
        return concept_restrictions(payload)
    if variant in {"And", "Or"}:
        result: list[dict[str, str]] = []
        for operand in payload:
            result.extend(concept_restrictions(operand))
        return result
    if variant in {"Exists", "Forall"}:
        role, filler = payload
        filler_variant, filler_payload = one_variant(filler)
        result = [{
            "kind": variant,
            "role": role_name(role),
            "filler_kind": filler_variant,
            "filler": filler_payload if isinstance(filler_payload, str) else "",
        }]
        result.extend(concept_restrictions(filler))
        return result
    if variant in {"AtLeast", "AtMost"}:
        cardinality, role, filler = payload
        filler_variant, filler_payload = one_variant(filler)
        result = [{
            "kind": f"{variant}:{cardinality}",
            "role": role_name(role),
            "filler_kind": filler_variant,
            "filler": filler_payload if isinstance(filler_payload, str) else "",
        }]
        result.extend(concept_restrictions(filler))
        return result
    if variant == "HasSelf":
        return [{
            "kind": "HasSelf",
            "role": role_name(payload),
            "filler_kind": "",
            "filler": "",
        }]
    raise ValueError(f"unsupported source concept: {value!r}")


def concept_shape(value: Any) -> str:
    variant, payload = one_variant(value)
    if variant in {"Name", "Top", "Bottom", "Nominal"}:
        return variant
    if variant == "Not":
        return f"Not({concept_shape(payload)})"
    if variant in {"And", "Or"}:
        return f"{variant}({','.join(concept_shape(item) for item in payload)})"
    if variant in {"Exists", "Forall"}:
        return f"{variant}(Role,{concept_shape(payload[1])})"
    if variant in {"AtLeast", "AtMost"}:
        return f"{variant}({payload[0]},Role,{concept_shape(payload[2])})"
    if variant == "HasSelf":
        return "HasSelf(Role)"
    raise ValueError(f"unsupported source concept: {value!r}")


def empty_object_node_truth(value: Any) -> bool:
    """Evaluate an expression with all object names/roles empty.

    This deliberately does not model datatype labels.  Callers use it only on
    source axioms without datatype concepts to identify object GCIs that would
    reject a blank data successor in the bridge's shared node domain.
    """
    variant, payload = one_variant(value)
    if variant == "Name" or variant == "Nominal":
        return False
    if variant == "Top":
        return True
    if variant == "Bottom":
        return False
    if variant == "Not":
        return not empty_object_node_truth(payload)
    if variant == "And":
        return all(empty_object_node_truth(item) for item in payload)
    if variant == "Or":
        return any(empty_object_node_truth(item) for item in payload)
    if variant == "Exists" or variant == "HasSelf":
        return False
    if variant == "Forall" or variant == "AtMost":
        return True
    if variant == "AtLeast":
        return int(payload[0]) == 0
    raise ValueError(f"unsupported source concept: {value!r}")


def concept_names(value: Any) -> set[str]:
    variant, payload = one_variant(value)
    if variant == "Name":
        return {payload}
    if variant in {"Top", "Bottom", "Nominal", "HasSelf"}:
        return set()
    if variant == "Not":
        return concept_names(payload)
    if variant in {"And", "Or"}:
        result: set[str] = set()
        for item in payload:
            result.update(concept_names(item))
        return result
    if variant in {"Exists", "Forall"}:
        return concept_names(payload[1])
    if variant in {"AtLeast", "AtMost"}:
        return concept_names(payload[2])
    raise ValueError(f"unsupported source concept: {value!r}")


class UnionFind:
    def __init__(self, values: Iterable[str]) -> None:
        self.parent = {value: value for value in values}

    def find(self, value: str) -> str:
        parent = self.parent.setdefault(value, value)
        if parent != value:
            self.parent[value] = self.find(parent)
        return self.parent[value]

    def union(self, left: str, right: str) -> None:
        left_root, right_root = self.find(left), self.find(right)
        if left_root != right_root:
            self.parent[right_root] = left_root

    def union_all(self, values: Iterable[str]) -> None:
        ordered = sorted(set(values))
        for value in ordered[1:]:
            self.union(ordered[0], value)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tin", type=Path, required=True)
    parser.add_argument("--tin-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    observed_sha256 = sha256_file(args.tin)
    if observed_sha256 != args.tin_sha256:
        raise SystemExit(
            f"TInput hash mismatch: expected {args.tin_sha256}, "
            f"observed {observed_sha256}"
        )
    tin = json.loads(args.tin.read_text(encoding="utf-8"))
    concepts: list[str] = tin.get("concepts") or []
    roles: list[str] = tin.get("roles") or []
    clauses: list[dict[str, Any]] = tin.get("clauses") or []
    source_axioms: list[dict[str, Any]] = tin.get("source_axioms") or []
    if len(roles) != len(set(roles)):
        raise SystemExit("TInput role names are not unique")

    range_assignments: dict[str, set[str]] = defaultdict(set)
    datatype_axioms: list[dict[str, Any]] = []
    all_restrictions: list[dict[str, Any]] = []
    unsupported_datatype_axioms: list[int] = []
    combined_datatype_axioms: list[int] = []
    non_datatype_top_axioms: list[dict[str, Any]] = []
    blank_data_node_violations: list[dict[str, Any]] = []
    for index, axiom in enumerate(source_axioms):
        left_restrictions = concept_restrictions(axiom["left"])
        right_restrictions = concept_restrictions(axiom["right"])
        restrictions = left_restrictions + right_restrictions
        for restriction in left_restrictions:
            all_restrictions.append(
                {"axiom_index": index, "side": "left", **restriction}
            )
        for restriction in right_restrictions:
            all_restrictions.append(
                {"axiom_index": index, "side": "right", **restriction}
            )
        datatype_restrictions = [
            restriction
            for restriction in restrictions
            if restriction["filler"].startswith("__dt__")
        ]
        source_datatype_names = {
            name
            for name in concept_names(axiom["left"])
            | concept_names(axiom["right"])
            if name.startswith("__dt__")
        }
        left_variant, _ = one_variant(axiom["left"])
        right_variant, _ = one_variant(axiom["right"])
        if not source_datatype_names:
            left_truth = empty_object_node_truth(axiom["left"])
            right_truth = empty_object_node_truth(axiom["right"])
            kind = axiom.get("kind")
            satisfied = (
                (not left_truth or right_truth)
                if kind == "sub-class"
                else left_truth == right_truth
            )
            row = {
                "index": index,
                "kind": kind,
                "left_shape": concept_shape(axiom["left"]),
                "right_shape": concept_shape(axiom["right"]),
                "left_truth": left_truth,
                "right_truth": right_truth,
            }
            if left_variant == "Top":
                non_datatype_top_axioms.append(row)
            if not satisfied:
                blank_data_node_violations.append(row)
        if not datatype_restrictions:
            continue
        if len(datatype_restrictions) > 1:
            combined_datatype_axioms.append(index)
        accepted = False
        if len(datatype_restrictions) == 1:
            restriction = datatype_restrictions[0]
            accepted = (
                (left_variant == "Name" and restriction["kind"] == "Exists")
                or (left_variant == "Top" and restriction["kind"] == "Forall")
            ) and right_variant in {"Exists", "Forall"}
            if left_variant == "Top" and restriction["kind"] == "Forall":
                range_assignments[restriction["role"]].add(
                    restriction["filler"]
                )
        datatype_axioms.append({
            "index": index,
            "kind": axiom.get("kind"),
            "left_variant": left_variant,
            "right_variant": right_variant,
            "restrictions": datatype_restrictions,
            "accepted_atomic_shape": accepted,
        })
        if not accepted:
            unsupported_datatype_axioms.append(index)

    range_roles = set(range_assignments)
    range_families = {
        role: sorted(
            name.removeprefix("__dt__").split("__", 1)[0]
            for name in names
        )
        for role, names in range_assignments.items()
    }
    range_role_domain_uses = []
    range_role_non_datatype_uses = []
    for restriction in all_restrictions:
        if restriction["role"] not in range_roles or restriction[
            "filler"
        ].startswith("__dt__"):
            continue
        # Source property-domain normalization is exactly
        # ``Exists(role, Top) -> domain``.  Its Top filler means any value in
        # the role's own range, not an object-range use of the data property.
        if (
            restriction["side"] == "left"
            and restriction["kind"] == "Exists"
            and restriction["filler_kind"] == "Top"
        ):
            range_role_domain_uses.append(restriction)
        else:
            range_role_non_datatype_uses.append(restriction)

    uf = UnionFind(roles)
    direct_edges: list[dict[str, Any]] = []
    for index, clause in enumerate(clauses):
        atoms = (clause.get("body") or []) + (clause.get("head") or [])
        role_ids = sorted({
            int(atom["r"])
            for atom in atoms
            if atom.get("k") in {"r", "e"}
        })
        distinct_roles = [roles[role_id] for role_id in role_ids]
        # Exist atoms connect a role to a filler, not to another role.  A
        # multi-role clause is the only direct clausal RBox bridge.
        if len(distinct_roles) > 1:
            uf.union_all(distinct_roles)
            if range_roles.intersection(distinct_roles):
                direct_edges.append({
                    "source": "clause",
                    "index": index,
                    "roles": distinct_roles,
                    "shape": {
                        "body": [atom.get("k") for atom in clause.get("body") or []],
                        "head": [atom.get("k") for atom in clause.get("head") or []],
                    },
                })
    for index, chain in enumerate(tin.get("chains") or []):
        chain_roles = [roles[int(role)] for role in chain]
        uf.union_all(chain_roles)
        if range_roles.intersection(chain_roles):
            direct_edges.append({
                "source": "chain", "index": index, "roles": chain_roles
            })

    components: dict[str, set[str]] = defaultdict(set)
    for role in roles:
        components[uf.find(role)].add(role)
    datatype_components = []
    cross_family_components = []
    for members in components.values():
        data_members = sorted(members & range_roles)
        if not data_members:
            continue
        families = sorted({
            family
            for role in data_members
            for family in range_families[role]
        })
        row = {
            "range_roles": data_members,
            "all_roles": sorted(members),
            "families": families,
        }
        datatype_components.append(row)
        if len(families) > 1:
            cross_family_components.append(row)

    role_source_counts = Counter(
        restriction["role"] for restriction in all_restrictions
    )
    top_shape_counts = Counter(
        (row["kind"], row["right_shape"])
        for row in non_datatype_top_axioms
    )
    violation_shape_counts = Counter(
        (row["kind"], row["left_shape"], row["right_shape"])
        for row in blank_data_node_violations
    )
    nominal_abox = tin.get("nominal_abox") or {}
    nominal_assertion_shapes = Counter(
        concept_shape(assertion)
        for individual in nominal_abox.get("individuals") or []
        for assertion in individual.get("assertions") or []
    )
    datatype_ids = {
        index for index, name in enumerate(concepts) if name.startswith("__dt__")
    }
    nominal_ids = set(int(value) for value in tin.get("nominals") or [])
    datatype_nominal_clause_indices = []
    for index, clause in enumerate(clauses):
        clause_concepts = {
            int(atom["c"])
            for atom in (clause.get("body") or []) + (clause.get("head") or [])
            if atom.get("k") in {"c", "e"}
        }
        if clause_concepts & datatype_ids and clause_concepts & nominal_ids:
            datatype_nominal_clause_indices.append(index)
    checks = {
        "nineteen_range_roles": len(range_roles) == 19,
        "one_range_per_role": all(
            len(names) == 1 for names in range_assignments.values()
        ),
        "all_datatype_axioms_atomic_supported_shape": (
            not unsupported_datatype_axioms
        ),
        "no_combined_datatype_source_axiom": not combined_datatype_axioms,
        "no_range_role_used_with_object_filler": (
            not range_role_non_datatype_uses
        ),
        "no_direct_cross_family_rbox_component": not cross_family_components,
        "no_datatype_nominal_clause": not datatype_nominal_clause_indices,
        "nominal_abox_complete": nominal_abox.get("complete") is True,
        "nominal_abox_has_only_top_assertions": set(nominal_assertion_shapes)
        <= {"Top"},
    }
    output = {
        "schema_version": 1,
        "status": "verified_structural_premises" if all(checks.values()) else "rejected",
        "supports_acceptance": False,
        "scope": "role-local datatype structural premises only",
        "tinput": str(args.tin),
        "tinput_sha256": observed_sha256,
        "counts": {
            "concepts": len(concepts),
            "roles": len(roles),
            "clauses": len(clauses),
            "source_axioms": len(source_axioms),
            "datatype_source_axioms": len(datatype_axioms),
            "range_roles": len(range_roles),
            "direct_edges_touching_range_roles": len(direct_edges),
            "datatype_role_components": len(datatype_components),
            "non_datatype_left_top_axioms": len(non_datatype_top_axioms),
            "blank_data_node_violations": len(blank_data_node_violations),
            "datatype_nominal_clauses": len(datatype_nominal_clause_indices),
            "nominal_individuals": len(nominal_abox.get("individuals") or []),
            "nominal_different_pairs": len(nominal_abox.get("different") or []),
        },
        "checks": checks,
        "range_assignments": {
            role: sorted(names) for role, names in sorted(range_assignments.items())
        },
        "range_families": dict(sorted(range_families.items())),
        "range_role_source_restriction_counts": {
            role: role_source_counts[role] for role in sorted(range_roles)
        },
        "datatype_components": sorted(
            datatype_components, key=lambda row: row["range_roles"]
        ),
        "direct_edges_touching_range_roles": direct_edges,
        "cross_family_components": cross_family_components,
        "unsupported_datatype_axiom_indices": unsupported_datatype_axioms,
        "combined_datatype_axiom_indices": combined_datatype_axioms,
        "range_role_non_datatype_uses": range_role_non_datatype_uses,
        "range_role_domain_uses": range_role_domain_uses,
        "non_datatype_left_top_shape_counts": [
            {"kind": key[0], "right_shape": key[1], "count": count}
            for key, count in sorted(top_shape_counts.items())
        ],
        "blank_data_node_violation_shape_counts": [
            {
                "kind": key[0],
                "left_shape": key[1],
                "right_shape": key[2],
                "count": count,
            }
            for key, count in sorted(violation_shape_counts.items())
        ],
        "blank_data_node_violation_examples": blank_data_node_violations[:100],
        "datatype_nominal_clause_indices": datatype_nominal_clause_indices,
        "nominal_abox_summary": {
            "complete": nominal_abox.get("complete"),
            "unsupported": nominal_abox.get("unsupported") or [],
            "individuals": len(nominal_abox.get("individuals") or []),
            "different_pairs": len(nominal_abox.get("different") or []),
            "assertion_shapes": dict(sorted(nominal_assertion_shapes.items())),
        },
        "fenced": tin.get("fenced") or [],
        "dropped": tin.get("dropped"),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps({
        "status": output["status"],
        "counts": output["counts"],
        "checks": checks,
        "cross_family_components": cross_family_components,
    }, sort_keys=True))
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
