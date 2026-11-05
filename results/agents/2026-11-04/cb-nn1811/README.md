# cb-nn1811: the nn1811 miss, a native-bridge defect behind a nominal route

## Status (third agent, 2026-11-05 09:35, interim)

State at takeover: commits 862ba3e5, ae5dbbae, 4b4cb4a3 and an uncommitted
engine edit with Lean (the CB repair `Engine::offer_root_reach`), which I
committed as 56cf6e56 after reading it. Done since: `lake build ContextCalculus`
(rc 0, no `sorryAx`), gap fixtures and tests (067201c3, 10 tests in
`engine/tests/cb_nn1811.rs` pass), NOMINALS-CB.md section 12 rewritten as
repaired, target seeds 20 of 20 on `ht_bridge` and the automatic route with the
CB repair (`data/targets-p1.tsv`).

Found by running the held-out inputs, which the earlier agents had not done:
ae5dbbae made ORE 3917 take more than 100 s (base 4.4 s). The cause is the
quadratic `add_entailed_functional_clauses` (gdb: `convert_with_rule_abox`), not the CB
repair. A linear rewrite with a reference test follows in the next commit. Every
measurement below that was taken with `km-p1` (the binary before that rewrite)
is void for timing and is repeated with the final binary.

## Status (continuation, 2026-11-04 23:55)

A second agent took over after the first stopped. State found:

- Committed: 862ba3e5 (reductions r1 to r19; bridge tests), ae5dbbae (the HT
  view carries entailed functionality, `cb_to_ht.rs`), 4b4cb4a3
  (docs/ROUTING.md "Entailed functionality in the HT view"; docs/NOMINALS-CB.md
  section 12 "An at-most with a filler at a nominal", ignored test).
- Uncommitted: `tools/pools.sh` (output directory, `DIFF_THREADS` override),
  `tools/detect_changed.py`, this README.
- Validation done before the stop: family gold (2,000 `fx` seeds), the base
  family run (one run, partly aborted) and three runs of `km-v1`; pool screen
  (13,959 of 19,790 seeds may change) and most of the `km-v1` pool rows
  (`pools/after/`, stopped inside `bridge-nn-rule-fam`). Not done: the 16
  held-out and 112 nominal ORE inputs, the test suite, the family summary
  (`FAMILY_PLACEHOLDER` below).
- Open: section 12 was recorded as "open". It is a wrong answer, not a
  decline: `--route nominals` answers m9, m11, m1, m6 to m10 without `⊤ ⊑ Q3`,
  and `certified_nominals`, which races the nominal CB arm against the bridge,
  publishes that answer when the CB arm wins (m9: 1 of 7 runs on `km-v1`, 3 of
  3 then 2 of 5 on `km-base`). So it is in scope and this continuation fixes it
  in the CB engine (section "The nominal CB filler gap" below).

Branch `fix/v155-cb-nn1811` from `development/v1.5.5` at 48a1113b, worktree
`.work/worktrees/fix-cb-nn1811`. Scratch: `.work/agent-scratch/cb-nn1811/`.
Release flags for every measurement: `KM_HT_DDB=1 KM_HT_NATIVE_FULL=1
KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1
KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1`. Binaries
(`.work/agent-scratch/cb-nn1811/bin/`): `km-base` = 48a1113b (sha256
a44ac18b…), `km-v1` = ae5dbbae (sha256 80a3af3f…; later commits change
docs, tests and results only). The engine sources of 48a1113b and ca64efb1
(the previous agent's `km-new`) are identical, so that agent's "after" pool
rows are a base for this branch.

## Gold (hand check)

nn1811: `InverseObjectProperties(r s)`, `InverseObjectProperties(r p)`, so
`s = p = r⁻`, and `⊤ ⊑ ≤1 r⁻` makes `s` functional.

- `Q4 ≡ ≤0 r` and `Q4 ≡ ≤1 r.(∃s.C)`. An `r`-successor `y` of `x` has `x`
  as its only `s`-successor, so `y ∈ ∃s.C` iff `x ∈ C`, and
  `≤1 r.(∃s.C) ≡ ¬C ⊔ ≤1 r`. With `Q4 ≡ ≤0 r` this gives `¬C ⊑ ≤0 r = Q4`;
  `DisjointClasses(A C)` gives `A ⊑ Q4`.
- `Q1 ≡ ≤3 s⁻.(∃p.{c})`: an `r`-successor of `x` is in `∃p.{c}` iff
  `x = c`, so `Q1 ≡ ¬{c} ⊔ ≤3 r ⊒ ≤0 r = Q4`: `Q4 ⊑ Q1`, `A ⊑ Q1`.
- `Q5 ≡ ≤1 s⁻.(∃s⁻.({b} ⊓ F))`: the elements with an `r`-successor `b` are
  `s`-successors of `b`, at most one, so `⊤ ⊑ Q5`.

HermiT's 13 pairs are these. A model with `c ∈ C` and four `r`-successors
of `c` (every element with an `r`-successor in `C` and at least two of them)
keeps `c ∉ Q1`; HermiT reports nothing more, and no further subsumption
follows from the axioms above. Every reduction below was checked against
HermiT 1.4 (`data/reductions/*.hermit.json`); r19 and r13 by hand as above.

## Cause

The wrong answer does not come from the nominal CB stack. On every run that
published it (the previous agent's and mine) the native bridge HT worker of
the `certified_nominals` race answered after 32 to 35 s
(`KM_TIMING race: HT worker exited @ 34.46s (success=true)`); in the runs
where that worker hit its 18 GiB cap the nominal CB arm gave no answer
within 150 s and the run timed out (`--route nominals` exceeds its RSS cap
as well). The previous agent's wrong automatic answers at 45 s and 58 s are
the 8.4 s bounded bridge-first attempt plus this 34 s answer.

Reductions (`data/reductions/`, 20 runs each, `data/reductions/runs20-*.txt`):

| input | axioms | HermiT | base: CB routes | base: bridge routes |
|---|---|---|---|---|
| r19 | `InverseObjectProperties(r s)`, `DisjointClasses(A C)`, `⊤ ⊑ ≤1 s`, `¬Q4 ⊑ ∃r.∃s.C` | `A ⊑ Q4` | right 20/20 | wrong 20/20 |
| r13 | as r19 with `≤1 r.(∃s.C) ⊑ Q4` | `A ⊑ Q4` | right | wrong |
| r1 | nn1811's six axioms on `r, s, p, A, C, Q4` | `A ⊑ Q4` | right | wrong |
| r3 | r1 plus `Q1 ≡ ≤3 s⁻.(∃p.{c})` | `A ⊑ Q1, A ⊑ Q4, Q4 ⊑ Q1` | `nominals` times out | wrong |
| r12 | r13 with `InverseFunctionalObjectProperty(r)` | `A ⊑ Q4` | right | wrong |
| r17 | r13 with `ObjectPropertyDomain(s ≤1 s)` | `A ⊑ Q4` | right | wrong |
| r5 | r13 with `FunctionalObjectProperty(s)` | `A ⊑ Q4` | right | right |

CB routes: `nominals`, `cb_plain1`, `nominal_ni_abox`,
`certified_card_proxy_abox`. Bridge routes: `ht_bridge`, `production_all`
(the automatic route of the TBox reductions), `certified_nominals`,
automatic. r19 has no individual: the defect is in the bridge on a
four-axiom SHI TBox with one global at-most.

Mechanism (`data/traces/`, `KM_SAT_ABSORB_DEBUG=1`): in the `A ⊓ ¬Q4` probe
the `r`-successor (node 1001) is satisfiable-cached from the earlier `C`
probe, and `SAT-ABSORB-CHECK parent=1001 concept-tag=19 role-tag=100 …
cached=true absorbable=true` absorbs `∃s.C`
(`completion/u22.rs` `is_generating_concept_satisfiable_cached_absorpable`,
a faithful port of Konclude cpp 14217). The successor that `≤1 s` would
merge into the parent is never built, so the parent never gets `C`. The test
refuses absorption only when the role to the ancestor is functional or an
at-most of it is already in the node's reapply queue. The bridge flags a role
functional only from the plain clause `R(x,y1) ∧ R(x,y2) → y1≈y2`
(`bridge.rs` functional scan), which only `FunctionalObjectProperty`
produces; `⊤ ⊑ ≤1 s` arrives as `Q_1(y1) ∧ Q_1(y2) ∧ Q_0(x) ∧ s(x,y1) ∧
s(x,y2) → y1≈y2` with `⊤` definers, from which the bridge builds a
`⊤`-qualified at-most (priority 3.5 instead of Konclude's 5.5 for an
unqualified `≤1`, so it is processed after the `∃`). Confirmed on the dumped
HT view (`KM_DUMP_TIN`) with the HT worker run standalone under the
`ht_bridge` bundle: the original view and a view with the qualifier removed
are wrong, a view with the plain clause added is right. The bridge is right
with `KM_HT_NO_SAT_EXP_CACHE=1`, `KM_BRIDGE_FRESH_ENV=1` or
`KM_HT_NO_SATURATION=1`, as on the previous agent's `nn1064`, `nn1313`,
`nn1348`. Konclude 0.7.0 does not finish TBox tasks on these inputs; it
answers the ABox form of r13 right.

## Fix (orchestrator, `orchestrate/cb_to_ht.rs`)

`add_entailed_functional_clauses` adds `R(0,1) ∧ R(0,2) → 1≈2` to the HT
view for every role whose functionality an at-most-1 clause of the view
entails with trivial guards: every concept atom of the clause is universal
(derived on every element from unit facts by one-variable Horn clauses) or
implied at its endpoint by the role atom (domain and range clauses, closed
under one-variable Horn clauses and the inverse and inclusion role clauses);
for the shared-target orientation (`InverseFunctionalObjectProperty`) it adds
the clause for every `S` with `S(0,1) → R(1,0)`. Every clause stays. The
argument is in docs/ROUTING.md ("Entailed functionality in the HT view"):
each added clause is a resolution consequence of the view, so the view has
the same models and every exact HT worker the same answer. The CB input, the
frontend output and the bridge are unchanged. Off under Lean HT certification
(the projection checker compares the view with its source clause by clause)
and with `KM_HT_NO_ENTAILED_FUNCTIONAL=1`. Not a CB calculus change, so no
Lean re-certification; the pass itself has no Lean proof (the bridge has no
Lean model).

Effect: nn1811 answers as HermiT in 0.1 s on the automatic route,
`ht_bridge` and `certified_nominals` (20 of 20 each); before, 34 s wrong or a
timeout. Every reduction answers as HermiT on every route that answers, 20
of 20 (`data/reductions/runs20-new.txt`).

What it does not cover: an at-most-1 with a real guard or filler
(`D ⊑ ≤1 s`, `⊤ ⊑ ≤1 s.D`) keeps its qualified encoding, and the bridge's
absorption test can still meet it before the at-most enters the reapply
queue. The complete repair belongs in the bridge (an agent on
`bridge-satcache` was running a family when I finished).

FAMILY_PLACEHOLDER
