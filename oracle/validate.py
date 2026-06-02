"""Validate the Rust disjunctive context-calculus engine against the HermiT
oracle.  For each ontology: normalise -> run Rust engine -> compare the entailed
atomic subsumptions (and consistency / unsatisfiable classes) with HermiT.

Soundness check  : every subsumption the engine reports must be in HermiT.
Completeness check: every HermiT subsumption the engine reports (subset OK; we
                    report the gap, which is expected for dropped chain/nominal
                    axioms that need the role-automaton / Table-3 extensions).
"""
from __future__ import annotations
import json, sys, time
from pathlib import Path

# Needs the (separate) `moose` package for SROIQ normalisation / OWL loading.
# Set MOOSE_HOME or place moose beside this repo.  The engine and the Lean proofs
# need no moose; only this HermiT cross-check (and the .ofn front-end) do.
import os
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "engine" / "py"))
_moose = ([Path(os.environ["MOOSE_HOME"])] if os.environ.get("MOOSE_HOME") else [])
_moose += [ROOT.parent / "moose", ROOT / "moose"]
for _c in _moose:
    if (_c / "moose" / "sroiq").is_dir():
        sys.path.insert(0, str(_c)); break

from moose.sroiq.normalisation import normalise
from moose.sroiq.owl_loader import load_ontology
from rust_context import rust_context_saturate
from preprocess import augment

ONTOS = {
    "disjunction": ROOT / "examples/ontologies/disjunction.ofn",
    "kinship_chain": ROOT / "examples/ontologies/kinship_chain.ofn",
    "kinship": ROOT / "examples/ontologies/kinship.ofn",
    "factor_test": ROOT / "oracle/ontologies/factor_test.ofn",
    "trans_test": ROOT / "oracle/ontologies/trans_test.ofn",
    "chain_test": ROOT / "oracle/ontologies/chain_test.ofn",
}


def short(n: str) -> str:
    return n.rsplit("#", 1)[-1].rsplit("/", 1)[-1]


def oracle_subs(name: str):
    j = json.loads((ROOT / "oracle/results" / f"{name}.json").read_text())
    subs = {}
    for a, b in j["subsumptions"]:
        subs.setdefault(short(a), set()).add(short(b))
    unsat = {short(c) for c in j.get("unsatisfiable", [])}
    return j["consistent"], subs, unsat


def engine_subs(path: Path):
    O = load_ontology(path).ontology
    tbox, abox, hooks = normalise(O)
    tbox = augment(tbox, abox, hooks)
    t0 = time.time()
    subs, _derived = rust_context_saturate(tbox)
    dt = time.time() - t0
    out = {}
    unsat = set()
    for a, sup in subs.items():
        a = short(a)
        for s in sup:
            if s in ("⊥", "owl:Nothing", "Nothing"):
                unsat.add(a)
            else:
                out.setdefault(a, set()).add(short(s))
    return out, unsat, dt, len(tbox)


def main():
    for name, path in ONTOS.items():
        if not path.exists():
            print(f"== {name}: MISSING {path}")
            continue
        try:
            o_cons, o_subs, o_unsat = oracle_subs(name)
        except FileNotFoundError:
            print(f"== {name}: no oracle result, skipping")
            continue
        try:
            e_subs, e_unsat, dt, nclauses = engine_subs(path)
        except Exception as ex:
            print(f"== {name}: ENGINE ERROR: {ex}")
            continue

        # flatten
        o_pairs = {(a, b) for a, bs in o_subs.items() for b in bs}
        e_pairs = {(a, b) for a, bs in e_subs.items() for b in bs}
        # restrict comparison to named classes HermiT knows about
        o_names = set(o_subs) | {b for bs in o_subs.values() for b in bs} | o_unsat
        # engine may include owl:Thing/internal; restrict to oracle's named universe for soundness
        unsound = {(a, b) for (a, b) in e_pairs if (a, b) not in o_pairs
                   and a in o_names and b in o_names}
        missing = o_pairs - e_pairs
        recovered = o_pairs & e_pairs

        print(f"== {name}  ({nclauses} clauses, {dt*1000:.1f} ms)")
        print(f"   consistency: oracle={o_cons}")
        print(f"   unsat: oracle={sorted(o_unsat)}  engine={sorted(e_unsat)}")
        print(f"   subsumptions: oracle={len(o_pairs)}  engine_recovered={len(recovered)}"
              f"  missing(incompleteness)={len(missing)}  UNSOUND={len(unsound)}")
        if unsound:
            print(f"   !!! UNSOUND PAIRS (engine claims, HermiT denies): {sorted(unsound)[:20]}")
        spurious_unsat = e_unsat - o_unsat
        if spurious_unsat:
            print(f"   !!! SPURIOUS UNSAT (engine claims unsat, HermiT says satisfiable): {sorted(spurious_unsat)}")
        if missing and len(missing) <= 30:
            print(f"   missing: {sorted(missing)}")


if __name__ == "__main__":
    main()
