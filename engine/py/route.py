#!/usr/bin/env python3
"""Hybrid router: classify an OWL ontology with whichever engine fits.

KM has two classifiers (see ``docs/HYBRID-TABLEAU.md``):

* the **CB engine** (``kobayashi-marust`` binary, via :mod:`owl_classify`) — a
  consequence-based reasoner that saturates *all* consequences in one pass. It is
  the fastest, most scalable choice for Horn / deterministic ontologies (EL, SH,
  SHQ, role hierarchy + transitivity + role chains + domain/range), but it blows
  up when disjunctions are *live* (the ``∀ + ⊔`` excluded-middle pattern): it
  materialises every branch of every successor, which is an *exponential memory*
  explosion, not merely a slow run. (Measured: the ``B_i ≡ ∀r.(C_i⊔C_{i+1})``
  stress test drove CB past 47 GB in seconds.)
* the **hypertableau** (``tableau_cli``, via :mod:`cb_to_ht`) — builds *one* model
  with backtracking + blocking. It terminates on the live-disjunction ontologies
  where CB explodes, and it is complete on the fragment ``cb_to_ht`` does not
  fence: ALC + H + SH/SHI (inverse) + SHQ (number) + SHO/SHOQ (nominals).

Why a static decision, not a try-CB-then-fall-back race: CB's blow-up is in
*memory*, so a wall-clock timeout cannot contain it — CB OOM-thrashes the whole
machine before the timeout fires. The router therefore decides up front from a
cheap static signal and never speculatively runs CB on a live-disjunction
ontology. Every CB invocation additionally runs under a hard address-space cap
(``--cb-mem-gb``) so a misjudged ontology fails with an allocation error instead
of taking the machine down.

Routing (one parse). The blow-up predictor is ``live`` = the number of
disjunctive clauses (head with >=2 concept disjuncts) whose body concept is a
**successor concept** (a concept the clause set asserts on a role-successor or
Skolem filler, i.e. on a term other than the centre ``x``). That is exactly the
``∀+⊔`` pattern that explodes: the disjunction fires afresh on every generated
successor. A top-level disjunction over root concepts (``live`` does not count it)
is cheap for CB to resolve once. Calibrated: the ``∀r.(C⊔C')`` stress test scores
``live=20`` while every CB-fast disjunctive ORE ontology (10006, 10123, 10140)
scores ``live=0`` — including 10140, whose CB-hardness is *size*, not disjunction.

0. **CB-incomplete in-fragment feature -> tableau.** The CB path is complete on
   EL/SH/SHQ + hierarchy/transitivity/chains/domain/range, but NOT on inverse
   roles (the engine never navigates inverse edges) or nominals (only the
   sound-but-incomplete ABox grounding). In-fragment ontologies with inverse or
   nominals go to the validated-complete tableau.
1. **live > 0 and in tableau fragment -> tableau.** Live disjunction; CB would
   explode in memory, so it is never speculatively run. The tableau builds one
   model and terminates. (The core of the user-requested routing.)
2. **otherwise -> CB**, under a hard address-space cap. ``live == 0`` covers all
   deterministic ontologies and the tame top-level-disjunction ones; a *large*
   deterministic ontology that is merely slow on CB is still a CB job (the tableau
   is slower per step and times out worse) — a scaling concern, orthogonal to
   routing. The cap is a host-safety backstop: should the static signal misjudge
   and CB overflow it, CB fails cleanly (no host OOM) and the router falls back to
   the tableau when the ontology is in-fragment, else reports ``cb-failed`` rather
   than a wrong answer.

Usage:  route.py [--cb-mem-gb G] [--explain] ontology.ofn
Output: {"engine": "cb"|"tableau"|"cb-failed", "consistent":..., "subsumptions":..., "unsatisfiable":...}
"""
from __future__ import annotations
import json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import frontend  # noqa: E402
import cb_to_ht  # noqa: E402
import owl_classify  # noqa: E402
import el_route  # noqa: E402  (EL++ completion fast path)

TABLEAU = HERE.parent / "target" / "release" / "tableau_cli"

# Hard address-space cap (GB) for every CB subprocess, so a misrouted
# live-disjunction ontology fails with an allocation error instead of OOMing the
# host. Generous (host-safety backstop, not a blow-up detector — that is `live`):
# defaults to ~60% of total RAM so legitimate large deterministic runs are not
# starved, while a runaway still cannot take the machine down.
def _default_cb_mem_gb():
    try:
        import os
        total = os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES")
        return max(4.0, 0.6 * total / (1 << 30))
    except Exception:
        return 8.0


DEFAULT_CB_MEM_GB = _default_cb_mem_gb()


def liveness(clauses):
    """Cheap static features predicting CB blow-up. ``live`` = disjunctive clauses
    whose body concept is a *successor concept* (asserted on a non-centre term,
    i.e. a role-successor or Skolem filler) — the ``∀+⊔`` pattern that makes the
    disjunction fire on every generated successor and explode."""
    succ = set()  # concepts asserted on a term other than the centre x
    for c in clauses:
        for a in c["head"]:
            if a.get("kind") == "concept":
                t = a["term"]
                if t.get("kind") == "fun" or (t.get("kind") == "var" and t.get("name") != "x"):
                    succ.add(a["concept"])
    ndisj = live = 0
    for c in clauses:
        if sum(1 for a in c["head"] if a.get("kind") == "concept") >= 2:
            ndisj += 1
            body_concepts = {a["concept"] for a in c["body"] if a.get("kind") == "concept"}
            if body_concepts & succ:
                live += 1
    return {"clauses": len(clauses), "ndisj": ndisj, "live": live}


def _mem_limit(gb):
    """preexec_fn that caps the child's virtual address space at ``gb`` GiB."""
    import resource
    n = int(gb * (1 << 30))
    resource.setrlimit(resource.RLIMIT_AS, (n, n))


def _filter_engine_out(out):
    """Shape an engine-style result ({"subsumptions": {C:[D,...]},
    "inconsistent": bool}) — produced by either the CB binary or the EL
    completion fast path — into the router's {consistent, subsumptions,
    unsatisfiable} form, dropping normalisation-internal names (the exact same
    filtering owl_classify applies)."""
    subs, unsat = [], []
    for a, sups in out["subsumptions"].items():
        if owl_classify.is_internal(a):
            continue
        sa = owl_classify.short(a)
        for s in sups:
            if owl_classify.is_semantic_bottom(s):
                if sa not in unsat:
                    unsat.append(sa)
            elif not owl_classify.is_internal(s) and owl_classify.short(s) != sa:
                subs.append([sa, owl_classify.short(s)])
    return {"consistent": not out.get("inconsistent", False),
            "subsumptions": sorted(subs), "unsatisfiable": sorted(unsat)}


def el_classify(clauses):
    """EL++ fast path: classify with moose's ELK-style completion (sound, low
    memory, no successor trees). Returns the shaped dict, or None if the clause
    set is not EL++ (caller falls through to CB/tableau)."""
    out = el_route.classify(clauses)
    return None if out is None else _filter_engine_out(out)


def cb_classify(clauses, mem_gb=DEFAULT_CB_MEM_GB):
    """Run the CB engine under a hard memory cap. Returns the classification
    dict, or None if the engine overflowed the cap / errored (never OOMs the
    host)."""
    import subprocess
    try:
        proc = subprocess.run([str(owl_classify.engine_path())],
                              input=json.dumps({"clauses": clauses}),
                              capture_output=True, text=True,
                              preexec_fn=lambda: _mem_limit(mem_gb))
    except Exception:
        return None
    if proc.returncode != 0 or not proc.stdout.strip():
        return None
    return _filter_engine_out(json.loads(proc.stdout))


def tableau_classify(tin):
    """Run the hypertableau. Returns the classification dict, or None on error."""
    import subprocess
    try:
        p = subprocess.run([str(TABLEAU)], input=json.dumps(tin),
                           capture_output=True, text=True)
    except Exception:
        return None
    if p.returncode != 0 or not p.stdout.strip():
        return None
    out = json.loads(p.stdout)

    def shrt(n):
        return n.rsplit("#", 1)[-1].rsplit("/", 1)[-1]

    return {"consistent": out["consistent"],
            "subsumptions": sorted([shrt(a), shrt(b)] for a, b in out["subsumptions"]),
            "unsatisfiable": sorted(shrt(x) for x in out["unsatisfiable"])}


def route(ofn, cb_mem_gb=DEFAULT_CB_MEM_GB, explain=False):
    clauses = frontend.ofn_to_clauses(ofn)
    rbox = frontend.ofn_rbox(ofn)
    feat = liveness(clauses)

    def finish(engine, res, why):
        if res is None:
            res = {"consistent": None, "subsumptions": [], "unsatisfiable": []}
            engine = engine + "-failed"
        if explain:
            res = dict(res)
            res["_features"] = feat
            res["_why"] = why
        res["engine"] = engine
        return res

    # EL++ fast path (cheapest, lowest memory, validated sound vs gold). EL is
    # Horn (no disjunctive heads => live=0) and the RBox-safe gate excludes
    # inverse/nominals, so an EL-safe ontology never needs the tableau; take it
    # straight to completion. Falls through if the clause set is not EL++ or the
    # RBox uses features moose folds only into the context engine.
    if el_route.is_el(clauses) and el_route.rbox_el_safe(rbox):
        res = el_classify(clauses)
        if res is not None:
            feat["in_tableau_fragment"] = None
            return finish("el", res, "EL++ via ELK-style completion")

    tin = cb_to_ht.convert(clauses, rbox)
    in_frag = not (tin["fenced"] or tin["dropped"])
    feat["in_tableau_fragment"] = in_frag
    feat["nominals"] = len(tin["nominals"])
    feat["inverse"] = tin["inverse"]

    # 0. CB-incomplete in-fragment feature -> tableau (validated-complete there).
    if in_frag and (tin["inverse"] or tin["nominals"]):
        why = "inverse (CB incomplete)" if tin["inverse"] else "nominals (CB incomplete)"
        return finish("tableau", tableau_classify(tin), why)
    # 1. live disjunction in the tableau fragment -> tableau. CB would explode in
    #    memory; never speculatively run it. This is the core routing decision.
    if feat["live"] > 0 and in_frag:
        return finish("tableau", tableau_classify(tin),
                      "live disjunction (live=%d); CB would blow up" % feat["live"])
    # 2. otherwise -> CB under the memory cap. Covers deterministic ontologies and
    #    tame (root-level) disjunction. The cap is a host-safety backstop: if the
    #    static signal misjudged and CB overflows, fall back to the tableau when
    #    in-fragment, else report cb-failed (never a wrong answer).
    res = cb_classify(clauses, cb_mem_gb)
    if res is not None:
        return finish("cb", res, "no live disjunction (live=0)" if feat["live"] == 0
                      else "live disjunction but tableau-fenced (CB best-effort)")
    if in_frag:
        return finish("tableau", tableau_classify(tin),
                      "CB overflowed %.0fGB cap; tableau fallback" % cb_mem_gb)
    reasons = sorted({f["reason"] for f in tin["fenced"]})
    return finish("cb", None, "CB overflowed cap, out of tableau fragment %s" % reasons)


def main():
    cb_mem_gb, explain, args = DEFAULT_CB_MEM_GB, False, []
    i = 1
    while i < len(sys.argv):
        a = sys.argv[i]
        if a == "--cb-mem-gb":
            cb_mem_gb = float(sys.argv[i + 1]); i += 2; continue
        if a == "--explain":
            explain = True; i += 1; continue
        if a.startswith("--"):
            i += 1; continue
        args.append(a); i += 1
    if len(args) != 1:
        print("usage: route.py [--cb-mem-gb G] [--explain] ontology.ofn", file=sys.stderr)
        sys.exit(2)
    print(json.dumps(route(args[0], cb_mem_gb, explain)))


if __name__ == "__main__":
    main()
