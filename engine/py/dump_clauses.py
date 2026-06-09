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


def canon(clauses):
    """Canonical, rename-invariant multiset of clauses, as sorted JSON lines.

    Renaming is *global* (one bijection over the whole clause set), so the
    structural linkage between clauses sharing an internal symbol is preserved.
    Body/head atoms are sorted within a clause (clauses are unordered conjunctions
    / disjunctions); clauses are then sorted as a multiset.
    """
    counters = {}
    def fresh(kind):
        counters[kind] = counters.get(kind, 0) + 1
        return counters[kind]
    ren = {}
    out = []
    for c in clauses:
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
