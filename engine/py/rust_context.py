"""Python adapter for the Rust `kobayashi-marust` binary.

Serialises `moose.sroiq.dlclauses` clauses (the normalised ``tbox``) to the JSON
schema reused from the sibling ``rust-saturation`` crate, runs the compiled
binary via ``subprocess``, and parses the results back into Python.

Exposes::

    rust_context_saturate(tbox) -> (subsumptions, derived_clauses)

where ``subsumptions`` is ``dict[str, set[str]]`` (concept -> entailed
superconcepts, including ``"⊥"`` for unsatisfiable concepts) and
``derived_clauses`` is ``list[moose.sroiq.dlclauses.ContextClause]``.

The crate is standalone; this adapter imports ``moose`` only for the clause
datatypes, which is permitted.
"""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import Iterable

from moose.sroiq import dlclauses as dlc


_CRATE_ROOT = Path(__file__).resolve().parent.parent


def _binary_path() -> Path:
    """Path to the release binary; build it if missing."""
    env = os.environ.get("SROIQ_CONTEXT_SATURATE_BIN")
    if env:
        return Path(env)
    candidate = _CRATE_ROOT / "target" / "release" / "kobayashi-marust"
    if not candidate.exists():
        subprocess.run(
            ["cargo", "build", "--release"],
            cwd=_CRATE_ROOT,
            check=True,
        )
    return candidate


# ---------------------------------------------------------------------------
# term / atom -> JSON
# ---------------------------------------------------------------------------


def _term_to_json(t: dlc.Term) -> dict:
    if isinstance(t, dlc.Variable):
        return {"kind": "var", "name": t.name}
    if isinstance(t, dlc.Individual):
        return {"kind": "ind", "name": t.name}
    if isinstance(t, dlc.AuxConstant):
        return {"kind": "aux", "root": t.root, "label": [[r, i] for (r, i) in t.label]}
    if isinstance(t, dlc.FunctionTerm):
        return {"kind": "fun", "function": t.function, "arg": _term_to_json(t.arg)}
    raise TypeError(f"unknown term: {type(t).__name__}")


def _atom_to_json(a: dlc.Atom) -> dict:
    if isinstance(a, dlc.ConceptAtom):
        return {"kind": "concept", "concept": a.concept, "term": _term_to_json(a.term)}
    if isinstance(a, dlc.RoleAtom):
        return {
            "kind": "role",
            "role": a.role,
            "source": _term_to_json(a.source),
            "target": _term_to_json(a.target),
        }
    if isinstance(a, dlc.EqAtom):
        return {
            "kind": "eq",
            "left": _term_to_json(a.left),
            "right": _term_to_json(a.right),
        }
    raise TypeError(f"unknown atom: {type(a).__name__}")


def _clause_to_json(c) -> dict:
    return {
        "body": [_atom_to_json(a) for a in c.body],
        "head": [_atom_to_json(a) for a in c.head],
    }


# ---------------------------------------------------------------------------
# JSON -> term / atom / clause
# ---------------------------------------------------------------------------


def _json_to_term(j: dict) -> dlc.Term:
    kind = j["kind"]
    if kind == "var":
        return dlc.Variable(j["name"])
    if kind == "ind":
        return dlc.Individual(j["name"])
    if kind == "aux":
        return dlc.AuxConstant(j["root"], tuple((r, i) for (r, i) in j["label"]))
    if kind == "fun":
        return dlc.FunctionTerm(j["function"], _json_to_term(j["arg"]))
    raise ValueError(f"unknown term kind: {kind}")


def _json_to_atom(j: dict) -> dlc.Atom:
    kind = j["kind"]
    if kind == "concept":
        return dlc.ConceptAtom(j["concept"], _json_to_term(j["term"]))
    if kind == "role":
        return dlc.RoleAtom(j["role"], _json_to_term(j["source"]), _json_to_term(j["target"]))
    if kind == "eq":
        return dlc.EqAtom(_json_to_term(j["left"]), _json_to_term(j["right"]))
    raise ValueError(f"unknown atom kind: {kind}")


def _json_to_clause(j: dict) -> dlc.ContextClause:
    return dlc.ContextClause(
        body=frozenset(_json_to_atom(a) for a in j["body"]),
        head=frozenset(_json_to_atom(a) for a in j["head"]),
    )


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------


def rust_context_saturate(
    tbox: Iterable[dlc.DLClause],
) -> tuple[dict[str, set[str]], list[dlc.ContextClause]]:
    """Run the context-based saturation over ``tbox`` via the Rust engine.

    Parameters
    ----------
    tbox
        Iterable of normalised ``DLClause`` / ``ContextClause`` (anything with
        ``.body`` and ``.head`` frozensets of atoms), as produced by
        ``moose.sroiq.normalisation.normalise``.

    Returns
    -------
    (subsumptions, derived_clauses)
        ``subsumptions``: ``dict[str, set[str]]`` mapping each concept name to
        its entailed superconcepts (``"⊥"`` present iff the concept is
        unsatisfiable).
        ``derived_clauses``: ``list[ContextClause]`` of the emitted
        consequences ``A(x) -> D(x)`` (and ``A(x) ->`` for clashes).
    """
    payload = {"clauses": [_clause_to_json(c) for c in tbox]}

    proc = subprocess.run(
        [str(_binary_path())],
        input=json.dumps(payload),
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"kobayashi-marust failed (rc={proc.returncode}): {proc.stderr}"
        )
    out = json.loads(proc.stdout)
    subsumptions = {k: set(v) for k, v in out["subsumptions"].items()}
    derived_clauses = [_json_to_clause(j) for j in out["derived_clauses"]]
    return subsumptions, derived_clauses
