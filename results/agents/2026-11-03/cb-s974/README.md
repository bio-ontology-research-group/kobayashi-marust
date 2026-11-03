# cb-s974: two wrong SELF-family answers (s974, s1966)

Branch `fix/v155-cb-s974` from `development/v1.5.5` at 117f143d, worktree
`.work/worktrees/fix-cb-s974`. Scratch: `.work/agent-scratch/cb-s974/`.
Release flags for every measurement: `KM_HT_DDB=1 KM_HT_NATIVE_FULL=1
KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1
KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`. Base binary: the merged 117f143d
binary `.work/v155-heldout-gap/selfmerge/km-117f143d`.

## s974: Q2 unsatisfiable, KM said satisfiable (CB engine)

### The gold holds

HermiT says `Q2` is unsatisfiable. Konclude (`~/konclude-build/Release/Konclude`,
the reference build) did not finish on s974 or s1966 within 60 s (it stays in
"Precomputing ontology ... expressiveness SIQ"; logs in `data/s974/`), and no
Openllet or JFact installation exists on ws (the reference audit ran them on
Ibex). The gold follows by hand from three axioms:

    Q2 ≡ E ⊓ ≥ 2 r.Self(p)      ReflexiveObjectProperty(r)
    InverseFunctionalObjectProperty(r)

Let `x ∈ Q2` with distinct r-successors `y1`, `y2`. Reflexivity gives
`r(y1,y1)`; inverse functionality on `r(x,y1)` and `r(y1,y1)` gives `x = y1`,
and likewise `x = y2`, so `y1 = y2`, a contradiction. HermiT also agrees on
the 3-axiom reduction `data/s974/m1.ofn` (`Q2 ⊑ ≥ 2 r`, `r` reflexive and
inverse functional: `Q2` unsatisfiable); the base binary answers it wrong too.

### Cause

The CB engine (route `production_all`, the in-process engine alone) derives
in the successor context `T → x ≈ y` (the successor equals its
predecessor) but never sends it to the predecessor: `pred_pool_eligible`
(`engine/src/engine.rs`) admitted predicates and the nominal forms
`x ≈ o`, `y ≈ o`, `o ≈ o'`, and kept `x ≈ y` local. arXiv:1805.01396,
Definition 2, puts `x ≈ y` in the predecessor triggers `Pr`, so the Pred
rule must deliver it, as `f(x) ≈ x`. Without it the predecessor learns the
consequences of the merge that the successor rewrote onto `y` (so
`Q2 ⊑ F` was found in a variant), but never that two successors `f1(x)` and
`f2(x)` both equal `x`, so the clause `Q_0(x) ∧ f1(x) ≈ f2(x) → ⊥` never
fires. Context dumps before and after: `data/s974/m1.{base,fixed}.dump.txt`
(after the fix context 0 holds `T → f(x) ≈ x` and `T → ⊥`).

### Fix and exactness

`pred_pool_eligible` admits `Eq{x, y}` (commit 4e5d6a46). The Lean
specification of the ordinary Pred send scan
(`lean/ContextCalculus/CBPredSendEnumeration.lean`,
`predHeadLiteralEligible`) admits the same literal, with kernel-evaluated
examples for `x ≈ y` (eligible), `y ≈ x` and `f(x) ≈ x` (not eligible).

- Soundness: if every element `e` described by the successor context with
  predecessor `d` satisfies `e = d`, then for the predecessor's element `d`
  and its successor `f(d)` along the edge, `f(d) = d`. This is the Pred rule
  of the paper instantiated with `L = x ≈ y ∈ Pr`.
- Completeness: the change restores the paper's `Pr`; KM's previous set was
  a strict subset, and the s974 family shows the gap.
- Order and termination: Definition 3, condition 6 constrains only atoms
  `A ≈ true ∈ Pr`; `x ≈ y` is not such an atom, so no ordering condition
  changes. `f(x) ≈ x` is already a context literal, so the set of derivable
  clauses stays finite.
- Lean build (`PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=4 nice taskset
  -c 17-24`): `lake build ContextCalculus` (8,659 jobs) and `lake build
  Validation` plus all 50 `cb-*` checkers and
  `ContextCalculus.CBCertificationSurface` (7,016 jobs) succeed; no
  `sorryAx` in either log; `mem_enumerate_iff` still depends only on
  `propext` and `Quot.sound`.
- Certified runs: `pred_triggers` in the CB certificate wire are the
  predicate triggers of the order (condition 6), not the Pred pool, so they
  stay predicates and `CBSourceHyperClosure`'s `pred_triggers_predicates`
  is unaffected. With `KM_LEAN_CHECKERS=<lean bin> KM_LEAN_CHECKERS_SET=all`
  the probes that derive `x ≈ y` (`data/probes/c1.ofn`, `c4.ofn`, s974,
  s1966, m1) publish with `cannot_check` events only (typed source
  declined, or "CB event has no chronological proof"); no checker rejected
  and none accepted, so the new literal never passes a checker unexamined.

## s1966: C ⊑ Q3 missing in about half of the runs (certified elc race)

### The gold holds

`ReflexiveObjectProperty(:r)` and `Q3 ≡ ∃r.Self` put every element in
`Q3`, so every class is under `Q3`, `C` included. HermiT agrees.

### Cause

`KM_TIMING` traces of a good and a bad run differ only in the engine block
(`data/s1966/timing.{good,bad}.err`: 9 subject rows after 0.11 s against 12
after 0.01 s). With `KM_THREADS=1` the CB stack is
`race::race_adaptive_vs_elc`: the full CB engine races the certified elc
worker (`KM_ELC_CERT=2`). On the absorbed clauses the certificate is partial
(exit 4): it publishes the subjects it could decide and hands the rest to a
query-restricted residue engine, whose answer is merged with the partial one.
Whichever of the full engine and the residue engine finishes first wins, which
is the run-to-run difference.

The partial answer was wrong. `C` occurs in one clause, `t(x,y) → C(x)`
(from `ObjectPropertyDomain(:t :C)`), and `t` occurs in no clause head. The
certificate's bridge preprocessing (`prepare_inverse_bridges`, vacuous-role
elimination) deletes that clause, which preserves the entailments of the
clause set, but `C` then occurs nowhere: it has no completion node, it is not
a certificate subject, it is not in the unresolved list, and the merged
answer publishes `C` with no superclass. The frontend emits a declaration
clause `C(x) → C(x)` only for a declared class that no other clause names,
so nothing restored `C`. `KM_ELC_SEQUENTIAL=1` (elc first, then its
residue) makes the wrong answer deterministic (4 of 4 on the base). The same
loss shows on the forced `elc_cert` route without any race:
`data/probes/top.ofn` (`⊤ ⊑ A`, `C` only in the domain of an unused role)
loses `C ⊑ A` on the base.

### Fix and exactness

`prepare_inverse_bridges` records the concept names of its input and appends
`C(x) → C(x)` for every name its rewrites removed (`retain_concept_signature`,
commit 4e5d6a46). A tautology adds no constraint, so the model class and the
entailments of the rewritten set are unchanged; the name gets its node, the
completion seeds it with the closure of `⊤`, and the certificate decides it
like every other named subject (on s1966 `C` now lands in the residue and the
engine answers it: `data/s1966/elc-cert.{base,fixed}.json`). The rewrites run
only in the non-Lean certificate modes (a checker-backed run keeps the exact
input stream), so no Lean statement is involved. Argued in
`docs/INVERSE-BRIDGE-CANONICALISATION.md`, "The rewrites must keep the
concept signature".

### Publication coverage guard (supervisor addition)

`orchestrate::undeclared_coverage` (commit a62e9ced, refined in f60acd77):
a consistent row-form worker answer (CB engine, elc and its residue merges)
that has no subject row for some declared class is declined
(`coverage guard: the worker answer omits N declared class(es)`), never
published. The elc worker now emits an empty row for every public concept
node (string map and compact output); the CB engine already did. HT, bridge
and tableau answers arrive as pair lists or as HT compact output without
empty rows, so absence carries no information there; they are marked
`pair_form` and stay outside the guard (an open protocol change: those
workers would have to report the query classes they decided). Argued in
`docs/ROUTING.md`, "Publication coverage guard". Unit test
`orchestrate::tests::coverage_guard_declines_an_answer_without_a_declared_class`
removes a class from a worker answer and checks the decline (plus the empty
row, unresolved and compact cases).
