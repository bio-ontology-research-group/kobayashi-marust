#!/usr/bin/env python3
"""Ground-truth oracle for the Rust normalisation frontend.

Prints `frontend.ofn_to_clauses(path)` as `{"clauses":[...]}` JSON — exactly the
payload the Rust frontend must reproduce (it is what owl_classify.py feeds to the
engine / EL completion). Use `--canon` to instead print a *canonical* form of the
clause set that is invariant under any consistent renaming of internal symbols
(`Q_*`, `f_*`, `__nom__*`, ...), so two frontends agree iff their canonical forms
are equal as multisets.

    python3 dump_clauses.py ont.ofn            # raw clauses JSON
    python3 dump_clauses.py --canon ont.ofn    # canonical clause multiset (sorted lines)
"""
from __future__ import annotations
import json, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import frontend  # noqa: E402

# Internal-symbol prefixes whose exact spelling is a frontend implementation
# detail (fresh counters / Skolem names). Two frontends are equivalent if their
# clause sets match after a *consistent* bijective renaming of these symbols.
_INTERNAL = ("Q_", "f_", "__nom__", "__inv__", "__conj__", "__trans__", "def_", "aux_")


def _is_internal_sym(s: str) -> bool:
    return any(s.startswith(p) for p in _INTERNAL)


def _term_key(t: dict, ren: dict, fresh):
    k = t["kind"]
    if k == "var":
        return ("v", t["name"])
    if k == "ind":
        return ("i", t["name"])
    if k == "fun":
        fn = t["function"]
        if _is_internal_sym(fn):
            fn = ren.setdefault(("f", fn), f"#f{fresh('f')}")
        return ("fn", fn, _term_key(t["arg"], ren, fresh))
    if k == "aux":
        return ("aux", t["root"], tuple(map(tuple, t["label"])))
    return (k,)


def _csym(s: str, ren: dict, fresh):
    if _is_internal_sym(s):
        return ren.setdefault(("c", s), f"#c{fresh('c')}")
    return s


def _atom_key(a: dict, ren: dict, fresh):
    k = a["kind"]
    if k == "concept":
        return ("C", _csym(a["concept"], ren, fresh), _term_key(a["term"], ren, fresh))
    if k == "role":
        r = a["role"]
        if _is_internal_sym(r):
            r = ren.setdefault(("r", r), f"#r{fresh('r')}")
        return ("R", r, _term_key(a["source"], ren, fresh), _term_key(a["target"], ren, fresh))
    if k == "eq":
        l = _term_key(a["left"], ren, fresh); rr = _term_key(a["right"], ren, fresh)
        return ("E", *sorted([l, rr]))
    raise ValueError(k)


def _skeleton(c: dict) -> str:
    """Order-independent fingerprint of a clause with every internal symbol
    blanked to its kind tag (so it does not depend on the emission order or on
    the concrete fresh-name spelling). Used to deterministically order clauses
    before assigning the global renaming bijection."""
    blank = {}
    n = [0]
    def f(_k):
        n[0] += 1
        return n[0]
    body = sorted(repr(_atom_key(a, blank, f)) for a in c["body"])
    head = sorted(repr(_atom_key(a, blank, f)) for a in c["head"])
    # collapse the per-clause fresh ids to a single token: only the *shape* and
    # the named (non-internal) symbols matter for ordering.
    import re as _re
    s = json.dumps({"b": body, "h": head}, sort_keys=True)
    return _re.sub(r"#[a-z]\d+", "#", s)


def canon(clauses):
    """Canonical, rename-invariant multiset of clauses, as sorted JSON lines.

    Renaming is *global* (one bijection over the whole clause set) so structural
    linkage between clauses sharing an internal symbol is preserved, and it is
    assigned in a deterministic, emission-order-independent order: clauses are
    first sorted by an internal-blanked skeleton, then the bijection is built
    walking that order. This makes the canonical form invariant to the order in
    which the two frontends happen to emit clauses (Python uses frozensets, so
    its emission order is hash-dependent and not reproducible in Rust).

    Body/head atoms are sorted within each clause (clauses are unordered
    conjunctions/disjunctions); clauses are sorted as a multiset at the end.
    """
    order = sorted(range(len(clauses)), key=lambda i: _skeleton(clauses[i]))
    counters = {}
    def fresh(kind):
        counters[kind] = counters.get(kind, 0) + 1
        return counters[kind]
    ren = {}
    out = []
    for i in order:
        c = clauses[i]
        body = sorted(repr(_atom_key(a, ren, fresh)) for a in c["body"])
        head = sorted(repr(_atom_key(a, ren, fresh)) for a in c["head"])
        out.append(json.dumps({"b": body, "h": head}, sort_keys=True))
    return sorted(out)


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    cl = frontend.ofn_to_clauses(args[0])
    if "--canon" in sys.argv[1:]:
        print("\n".join(canon(cl)))
    else:
        print(json.dumps({"clauses": cl}))
