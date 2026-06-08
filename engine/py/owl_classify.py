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
    s = frontend.local_name(n)
    return s.rsplit("#", 1)[-1].rsplit("/", 1)[-1]


def is_internal(n: str) -> bool:
    # A name backed by a real OWL IRI is a real class, even if its local name
    # happens to match a moose-internal prefix (e.g. a `Q_minus`/`Q_plus` class
    # in symbols.owl). Only un-IRI-backed names get the prefix heuristic.
    if frontend.is_named_iri(n):
        return False
    s = short(n)
    return (s.startswith("Q_") or s.startswith("__") or s.startswith("aux_")
            or s.startswith("def_") or (":" in s and s not in BOTTOM))


def _race_el(clauses_json: str):
    """For EL++ ontologies, race the context-engine binary against the EL
    completion reasoner and return the first valid result; kill the loser. Both
    are sound+complete on EL++, but neither dominates on time — completion wins
    on transitive / blow-up ontologies, the context engine wins on some large
    flat ones. Racing captures both with no regression. Returns the parsed dict
    or None (caller then runs the binary alone)."""
    import threading
    import time
    here = Path(__file__).resolve().parent
    cmds = {"el": [sys.executable, str(here / "el_route.py")],
            "ctx": [str(engine_path())]}
    boxes = {k: {} for k in cmds}

    def run(key):
        box = boxes[key]
        try:
            p = subprocess.Popen(cmds[key], stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            box["proc"] = p
            out, _ = p.communicate(clauses_json)   # reads fully -> no pipe deadlock
            box["rc"] = p.returncode
            box["out"] = out
        except Exception:
            box["rc"] = -1

    threads = {k: threading.Thread(target=run, args=(k,), daemon=True) for k in cmds}
    for t in threads.values():
        t.start()
    winner = None
    # poll for the first thread to finish successfully (prefer completion on tie)
    while winner is None and any(t.is_alive() for t in threads.values()):
        for key in ("el", "ctx"):
            if not threads[key].is_alive() and boxes[key].get("rc") == 0:
                winner = key
                break
        else:
            time.sleep(0.05)
    if winner is None:  # both finished; pick any success
        for key in ("el", "ctx"):
            if boxes[key].get("rc") == 0:
                winner = key
                break
    # kill the loser
    for key in cmds:
        if key != winner:
            p = boxes[key].get("proc")
            if p is not None and p.poll() is None:
                p.kill()
    if winner is None:
        return None
    return json.loads(boxes[winner]["out"])


def classify(ofn_path: str) -> dict:
    clauses = frontend.ofn_to_clauses(ofn_path)
    clauses_json = json.dumps({"clauses": clauses})
    out = None
    # EL fast path. If the ontology is EL++:
    #  - with transitive roles, the context engine reliably blows up, so go
    #    straight to completion;
    #  - otherwise race the context engine against completion and take the
    #    faster (neither dominates on flat EL; racing avoids regressing the
    #    ontologies the context engine already handles quickly).
    if el_route.is_el(clauses):
        if el_route.has_transitivity(clauses):
            out = el_route.classify(clauses)
        else:
            out = _race_el(clauses_json)
    if out is None:
        proc = subprocess.run([str(engine_path())],
                              input=clauses_json,
                              capture_output=True, text=True)
        if proc.returncode != 0:
            raise RuntimeError(proc.stderr)
        out = json.loads(proc.stdout)

    subs, unsat = [], []
    for a, sups in out["subsumptions"].items():
        if is_internal(a):
            continue
        sa = short(a)
        for s in sups:
            if short(s) in BOTTOM:
                if sa not in unsat:
                    unsat.append(sa)
            elif not is_internal(s) and short(s) != sa:
                subs.append([sa, short(s)])
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
