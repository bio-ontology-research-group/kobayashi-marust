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
import json, os, subprocess, sys, tempfile
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


def elc_bin() -> str:
    env = os.environ.get("KM_ELC_BIN")
    if env:
        return env
    return str(HERE.parent / "target" / "release" / "elc")


def run_ofn_split(ofn_path: str):
    """Run `ofn` in split mode: the (large) clause set goes to a temp file in
    the engine/elc stdin shape `{"clauses":[...]}`, and the small side data
    {iri_map, named, declared, el_rbox_safe} is returned as a dict. Returns
    (clauses_path, meta); the caller owns clauses_path and must unlink it. This
    keeps the clause set out of Python entirely — parsing+re-serialising it
    dominated the EL fast path on large ontologies. Exit 3 => out of fragment."""
    cfd, clauses_path = tempfile.mkstemp(suffix=".clauses.json")
    os.close(cfd)
    mfd, meta_path = tempfile.mkstemp(suffix=".meta.json")
    os.close(mfd)
    try:
        with open(clauses_path, "w") as cf:
            proc = subprocess.run([ofn_bin(), ofn_path, "--meta", meta_path],
                                  stdout=cf, stderr=subprocess.PIPE, text=True)
        if proc.returncode == 3:
            os.unlink(clauses_path)
            raise frontend.OutOfFragment(proc.stderr.strip() or "out of fragment")
        if proc.returncode != 0:
            os.unlink(clauses_path)
            raise RuntimeError(proc.stderr)
        with open(meta_path) as mf:
            meta = json.load(mf)
        return clauses_path, meta
    finally:
        if os.path.exists(meta_path):
            os.unlink(meta_path)


def run_reasoner_file(argv, clauses_path):
    """Run a reasoner binary (elc or the context engine) reading the clause set
    straight from `clauses_path` via stdin (no Python serialisation)."""
    with open(clauses_path) as f:
        return subprocess.run(argv, stdin=f, capture_output=True, text=True)


def classify(ofn_path: str) -> dict:
    # Front-end: Rust `ofn` binary (fast; env-gated) or the Python normaliser.
    # Both yield the same clause set plus the output-mapping data (full IRI of
    # each internal name, the set of IRI-backed names, RBox EL-safety). The Rust
    # path avoids the 45-100s Python parse+normalise on large ontologies.
    use_rust_el = bool(os.environ.get("KM_RUST_EL"))
    clauses_path = None  # set in the zero-copy path; clauses then stay out of Python
    clauses = None
    if os.environ.get("KM_RUST_FRONTEND"):
        if use_rust_el:
            # Zero-copy: ofn writes the clause set to a file and the small side
            # data to a meta file; Python reads only the meta. elc / the engine
            # read the clauses straight from the file (no parse+re-dump in Python).
            clauses_path, meta = run_ofn_split(ofn_path)
            _iri_map = meta["iri_map"]
            _named = set(meta["named"])
            rbox_safe = bool(meta["el_rbox_safe"])
        else:
            data = run_ofn(ofn_path)
            clauses = data["clauses"]
            _iri_map = data["iri_map"]
            _named = set(data["named"])
            rbox_safe = bool(data["el_rbox_safe"])
        full_iri = lambda n: _iri_map.get(n, n)          # noqa: E731
        named_iri = lambda n: n in _named                # noqa: E731
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

    try:
        out = None
        # EL fast path: classify EL++ ontologies with the ELK-style completion.
        # The compiled `elc` decides EL-membership itself (exit 3 => not EL, fall
        # through to the context engine); it replaces the Python completion on the
        # large EL ontologies whose Python saturation exceeds the time budget.
        if rbox_safe and use_rust_el:
            proc = run_reasoner_file([elc_bin()], clauses_path)
            if proc.returncode == 3:
                out = None
            elif proc.returncode != 0:
                raise RuntimeError(proc.stderr)
            else:
                out = json.loads(proc.stdout)
        elif el_route.is_el(clauses) and rbox_safe:
            out = el_route.classify(clauses)
        if out is None:
            if clauses_path is not None:
                proc = run_reasoner_file([str(engine_path())], clauses_path)
            else:
                proc = subprocess.run([str(engine_path())],
                                      input=json.dumps({"clauses": clauses}),
                                      capture_output=True, text=True)
            if proc.returncode != 0:
                raise RuntimeError(proc.stderr)
            out = json.loads(proc.stdout)
    finally:
        if clauses_path is not None and os.path.exists(clauses_path):
            os.unlink(clauses_path)

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
