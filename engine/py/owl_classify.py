#!/usr/bin/env python3
"""OWL → classification bridge for the Protege plugin (and CLI use).

Reads an OWL functional-syntax (`.ofn`) ontology, runs the *real* normalisation
front-end (`frontend.ofn_to_clauses`, reusing moose's `normalise` + `augment`),
invokes the `kobayashi-marust` engine, and prints a compact JSON classification
of the **named** concepts on stdout:

    { "consistent": <bool>,
      "subsumptions": [ ["Sub","Super"], ... ],   # named atomic A ⊑ B (B != A)
      "unsatisfiable": [ "C", ... ] }

Normalisation-internal concepts (`Q_*`, `__*`, prefixed builtins) are filtered
out, so the result is in terms of the ontology's own class names.

Usage:  python3 owl_classify.py ontology.ofn
Env:    KM_ENGINE  path to the kobayashi-marust binary (else autodetected).
"""
from __future__ import annotations
import json, os, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import frontend  # noqa: E402  (parse/normalise/augment; locates moose itself)
import el_route  # noqa: E402  (EL++ fast path via moose's completion reasoner)

BOTTOM = {"Nothing", "owl:Nothing", "⊥"}


def engine_path() -> Path:
    env = os.environ.get("KM_ENGINE")
    if env:
        return Path(env)
    # engine/py/ -> engine/target/release/kobayashi-marust
    for name in ("kobayashi-marust", "sroiq-context-saturate"):
        p = HERE.parent / "target" / "release" / name
        if p.exists():
            return p
    raise FileNotFoundError(
        "kobayashi-marust binary not found; set KM_ENGINE or run "
        "`cargo build --release` in engine/."
    )


def short(n: str) -> str:
    # Collapse the engine-internal name back to its OWL local name. frontend
    # disambiguates distinct IRIs that share a fragment (sound reasoning), but
    # the classification output must use the bare local name to match the gold
    # comparison convention (ore_canon.localname). See frontend.local_name.
    #
    # local_name == _short_base(full IRI), which already implements the gold
    # ore_canon.localname convention exactly: everything after the last '#', or
    # (if there is no '#') after the last '/'. Crucially it keeps the whole
    # post-'#' fragment, including any embedded '/' or '://' — ORE surrogate
    # classes look like '…obo/_#_hasValue__http://…/SWO_0000394__http://…/SWO_0000023'
    # and gold keeps that full fragment. The old code did an extra
    # `.rsplit('/')`, truncating such fragments to their last path segment
    # ('C2/C3_facet_joint' -> 'C3_facet_joint'; the _hasValue surrogate ->
    # 'SWO_0000023'), which showed as spurious extra+missing vs gold (ore_ont_14499,
    # 8135). Return local_name unchanged so output matches the gold convention.
    return frontend.local_name(n)


def is_internal(n: str) -> bool:
    # A name backed by a real OWL IRI is a real class, even if its local name
    # happens to match a moose-internal prefix (e.g. a `Q_minus`/`Q_plus` class
    # in symbols.owl). Only un-IRI-backed names get the prefix heuristic.
    if frontend.is_named_iri(n):
        return False
    s = short(n)
    return (s.startswith("Q_") or s.startswith("__") or s.startswith("aux_")
            or s.startswith("def_") or (":" in s and s not in BOTTOM))


def ofn_bin() -> str:
    env = os.environ.get("KM_OFN_BIN")
    if env:
        return env
    return str(HERE.parent / "target" / "release" / "ofn")


def run_ofn(ofn_path: str) -> dict:
    """Run the Rust `ofn` normalisation frontend; returns its
    {clauses, iri_map, named, declared, el_rbox_safe} dict. Exit 3 means the
    ontology is out of the supported fragment (datatypes), mirroring
    frontend.OutOfFragment."""
    proc = subprocess.run([ofn_bin(), ofn_path], capture_output=True, text=True)
    if proc.returncode == 3:
        raise frontend.OutOfFragment(proc.stderr.strip() or "out of fragment")
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    return json.loads(proc.stdout)


def classify(ofn_path: str) -> dict:
    # Front-end: Rust `ofn` binary (fast; env-gated) or the Python normaliser.
    # Both yield the same clause set plus the output-mapping data (full IRI of
    # each internal name, the set of IRI-backed names, RBox EL-safety). The Rust
    # path avoids the 45-100s Python parse+normalise on large ontologies.
    if os.environ.get("KM_RUST_FRONTEND"):
        data = run_ofn(ofn_path)
        clauses = data["clauses"]
        _iri_map = data["iri_map"]
        _named = set(data["named"])
        full_iri = lambda n: _iri_map.get(n, n)          # noqa: E731
        named_iri = lambda n: n in _named                # noqa: E731
        rbox_safe = bool(data["el_rbox_safe"])
    else:
        clauses = frontend.ofn_to_clauses(ofn_path)
        full_iri = frontend.full_iri
        named_iri = frontend.is_named_iri
        rbox_safe = el_route.rbox_el_safe(frontend.ofn_rbox(ofn_path))

    def is_internal(n: str) -> bool:
        # A name backed by a real OWL IRI is a real class even if its local name
        # matches a moose-internal prefix; only un-IRI-backed names get the
        # prefix heuristic. Uses the active frontend's IRI-backed-name predicate.
        if named_iri(n):
            return False
        s = short(n)
        return (s.startswith("Q_") or s.startswith("__") or s.startswith("aux_")
                or s.startswith("def_") or (":" in s and s not in BOTTOM))

    clauses_json = json.dumps({"clauses": clauses})
    out = None
    # EL fast path: classify EL++ ontologies with moose's ELK-style completion
    # (el_route). With the predecessor-index optimisation completion is fast on
    # every EL ontology in the corpus (flat and transitive alike), so we use it
    # directly. A race against the context-engine binary was tried but its 16
    # rayon threads starve the single-threaded completion under the benchmark's
    # KM_THREADS=16, so completion-only is both faster and simpler here.
    if el_route.is_el(clauses) and rbox_safe:
        out = el_route.classify(clauses)
    if out is None:
        proc = subprocess.run([str(engine_path())],
                              input=clauses_json,
                              capture_output=True, text=True)
        if proc.returncode != 0:
            raise RuntimeError(proc.stderr)
        out = json.loads(proc.stdout)

    # Output uses the FULL IRI (frontend.full_iri); the comparison harness
    # applies ore_canon.localname once, exactly as it does for every other
    # reasoner. Filtering (is_internal) and the self-/bottom-subsumption checks
    # stay on the short local name. Emitting the short name here instead made the
    # harness localname-truncate fragments containing '/' (ore_ont_14499/8135).
    subs, unsat = [], []
    for a, sups in out["subsumptions"].items():
        if is_internal(a):
            continue
        sa = short(a)
        fa = full_iri(a)
        for s in sups:
            if short(s) in BOTTOM:
                if fa not in unsat:
                    unsat.append(fa)
            elif not is_internal(s) and short(s) != sa:
                subs.append([fa, full_iri(s)])
    return {
        "consistent": not out.get("inconsistent", False),
        "subsumptions": sorted(subs),
        "unsatisfiable": sorted(unsat),
        "dropped": out.get("dropped", 0),
    }


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    lines = "--lines" in sys.argv[1:]
    if len(args) != 1:
        print("usage: owl_classify.py [--lines] ontology.ofn", file=sys.stderr)
        sys.exit(2)
    try:
        res = classify(args[0])
    except frontend.OutOfFragment as e:
        # honest decline: the ontology is outside the supported fragment
        # (datatypes). Report unsupported rather than a partial classification.
        print(f"unsupported: {e}", file=sys.stderr)
        sys.exit(3)
    if lines:
        # Dependency-free line format for the Java/Protege plugin:
        out = [f"CONSISTENT {1 if res['consistent'] else 0}",
               f"DROPPED {res['dropped']}"]
        out += [f"SUB\t{a}\t{b}" for a, b in res["subsumptions"]]
        out += [f"UNSAT\t{c}" for c in res["unsatisfiable"]]
        print("\n".join(out))
    else:
        print(json.dumps(res))
