"""EL fast path: route ontologies that lie in the EL++ fragment to moose's
native ELK-style completion reasoner instead of the disjunctive context engine.

Why
---
The context engine (a port of Sequoia's disjunctive context calculus) is sound
and complete on all of SROIQ, but its handling of *transitive roles* — encoded
by moose's normalisation as ``__trans__r__C`` propagation concepts — generates
unbounded redundant Pred/Succ inter-context message traffic on large EL
ontologies. Context count stabilises but the message fixpoint does not converge
in practical time (e.g. ore_ont_11497: 105 classes, 240 s+ timeout). The same
ontology is classified exactly and in seconds by the ELK-style EL++ completion
procedure (``moose.elpp.completion``), which saturates told-subsumer sets in
O(n^3) without materialising successor trees or passing messages.

How
---
The frontend already normalises the ontology into Horn DL-clauses. When the
ontology is in EL++, *every* clause has one of a small set of shapes that map
directly onto the EL++ normal forms NF1-NF7. :func:`to_nf` performs that map;
if any clause falls outside it (disjunction in the head, equality/number atoms,
nominal ``ind`` terms, ...) the ontology is *not* EL and :func:`classify`
returns ``None`` so the caller falls back to the context engine. The map is
therefore a sound, conservative router: it only fires when the whole clause set
is EL++, in which case the completion result coincides with the context
engine's (validated against the Konclude gold standard on the ORE 2015 sweep).

The translation consumes the *frontend's own* normalised clauses, so role
hierarchy, transitivity (``__trans`` concepts → NF4 rules the completion engine
discharges efficiently), domain/range, and the isolated-class self-clauses are
all carried through with no separate parser.
"""
from __future__ import annotations

from moose.elpp.axioms import NF1, NF2, NF3, NF4, NF5, NF6, NF7, TOP, BOTTOM
from moose.elpp.completion import Completion


def _tk(t):
    """Term kind: ('var', name) | ('fun', f, argvar|None) | (otherkind,)."""
    k = t["kind"]
    if k == "var":
        return ("var", t["name"])
    if k == "fun":
        a = t["arg"]
        return ("fun", t["function"], a.get("name") if a.get("kind") == "var" else None)
    return (k,)  # ind / aux: not an EL normal-form tree term


def to_nf(clauses):
    """Map frontend DL-clauses to EL++ normal forms. Returns ``(axioms, ok)``;
    ``ok`` is False (and axioms None) as soon as any clause is outside EL++."""
    ax = []
    pending_ex = {}  # (sub_concept, skolem_fn) -> {'role':R, 'filler':B}
    for c in clauses:
        b = c["body"]
        h = c["head"]
        # equality / inequality atoms (number restrictions, nominals merge) -> not EL
        if any(a["kind"] not in ("concept", "role") for a in b + h):
            return None, False
        bc = [a for a in b if a["kind"] == "concept"]
        br = [a for a in b if a["kind"] == "role"]
        hc = [a for a in h if a["kind"] == "concept"]
        hr = [a for a in h if a["kind"] == "role"]
        # empty head => ⊥ (NF5 / disjointness)
        if len(h) == 0:
            if len(bc) == 1 and not br:
                ax.append(NF5(bc[0]["concept"]))
                continue
            if len(bc) == 2 and not br:
                ax.append(NF2(bc[0]["concept"], bc[1]["concept"], BOTTOM))
                continue
            return None, False
        # disjunctive head => not EL (Horn only)
        if len(h) != 1:
            return None, False
        # ---- concept head ----
        if hc:
            ht = _tk(hc[0]["term"])
            hd = hc[0]["concept"]
            if ht[0] == "var":
                if not br and all(_tk(a["term"])[0] == "var" for a in bc):
                    if len(bc) == 0:
                        ax.append(NF1(TOP, hd)); continue           # ⊤ ⊑ B
                    if len(bc) == 1:
                        ax.append(NF1(bc[0]["concept"], hd)); continue   # A ⊑ B
                    if len(bc) == 2:
                        ax.append(NF2(bc[0]["concept"], bc[1]["concept"], hd)); continue  # A⊓A' ⊑ B
                    return None, False
                # NF4:  R(x,y) ∧ A(y) ⊑ B(x)
                if len(br) == 1 and len(bc) == 1:
                    r = br[0]; cc = bc[0]
                    sx, sy = _tk(r["source"]), _tk(r["target"])
                    if sx[0] == "var" and sy[0] == "var" and _tk(cc["term"]) == sy:
                        ax.append(NF4(r["role"], cc["concept"], hd)); continue
                return None, False
            if ht[0] == "fun":  # existential filler: A(x) -> B(f(x))
                if len(bc) == 1 and not br and _tk(bc[0]["term"])[0] == "var":
                    pending_ex.setdefault((bc[0]["concept"], ht[1]), {})["filler"] = hd
                    continue
                return None, False
            return None, False
        # ---- role head ----
        if hr:
            r = hr[0]
            st = _tk(r["target"]); sxs = _tk(r["source"])
            # existential role: A(x) -> R(x, f(x))
            if (st[0] == "fun" and sxs[0] == "var" and len(bc) == 1 and not br
                    and _tk(bc[0]["term"])[0] == "var"):
                pending_ex.setdefault((bc[0]["concept"], st[1]), {})["role"] = r["role"]
                continue
            # role inclusion: R(x,y) -> S(x,y)
            if st[0] == "var" and len(br) == 1 and not bc:
                ax.append(NF6(br[0]["role"], r["role"])); continue
            # role chain: R(x,y) ∧ S(y,z) -> T(x,z)
            if st[0] == "var" and len(br) == 2 and not bc:
                ax.append(NF7(br[0]["role"], br[1]["role"], r["role"])); continue
            return None, False
        return None, False
    # assemble NF3 (A ⊑ ∃R.B) from its two half-clauses
    for (sub, _fn), d in pending_ex.items():
        if "role" in d:
            ax.append(NF3(sub, d["role"], d.get("filler", TOP)))
        else:
            return None, False  # filler with no role edge: shape we don't model
    return ax, True


def classify(clauses):
    """If `clauses` is EL++, classify with completion and return a dict shaped
    like the context engine's JSON output (``{"subsumptions": {C:[D,...]},
    "inconsistent": bool}``). Otherwise return None."""
    ax, ok = to_nf(clauses)
    if not ok:
        return None
    res = Completion(ax).saturate()
    subs = {}
    for c, sups in res.sub_super.items():
        out = []
        for d in sups:
            if d == c or d == TOP:
                continue
            out.append("owl:Nothing" if d == BOTTOM else d)
        if out:
            subs[c] = out
    return {"subsumptions": subs, "inconsistent": res.is_unsatisfiable(TOP), "dropped": 0}
