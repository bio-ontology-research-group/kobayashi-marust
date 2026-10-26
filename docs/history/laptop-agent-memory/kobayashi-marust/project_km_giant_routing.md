---
name: project_km_giant_routing
description: "ALL THREE ORE giants (8737/15059/16744) recovered: streaming frontend + Skolem-exclusion EL routing + clone-free elc; history of the relevance-slice design"
metadata:
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-10, branch payg-strategy. Goal: route the two ORE giants (8737/16744,
2.5-3.1M axioms) to `elc` instead of the CB engine, where they time out at 240s.

**The giants are pure EL except** `SymmetricObjectProperty(RO_0002158)` (also
transitive, used in 2.5-3.1M superclass-side existentials `C ⊑ ∃RO_0002158.D`)
and `InverseObjectProperties(part_of=BFO_0000050, has_part=BFO_0000051)`
(has_part appears ONLY in the inverse decl; part_of also `⊑ RO_0002131` and is
transitive). No domain/range, no `∀`, no subclass-side existentials,
no cardinality/disjointness/complement.

**Landed (commit `e59d7fa`): sound role-relevance routing relaxation.**
`preprocess::concept_relevant_roles` marks a role relevant if it sits in a
clause body with a concept/eq head, or feeds such a role via a role-headed
clause (subrole/chain/transitivity/inverse-bridge). An inert symmetric/inverse
role gets its reverse-edge clauses pruned (`prune_inert_role_bridges`) and
`rbox::el_rbox_safe_relaxed` admits the ontology to elc. Conservative: onts with
no symmetric/inverse roles get the identical decision as before; routing an
inert case to elc is sound (weaker theory). 5 unit tests; soundness table did
NOT regress (became 552 agree / 6 incomplete / 4 unsound / 0 both-disagree).

**But it does NOT fire on the giants** (verified via a KM_OFN_RELEVANCE_DEBUG
build, since removed). `el_rbox_safe=false` because RO_0002158 is marked
relevant. Root cause: `preprocess::transitivity_clauses` AND the normaliser's
`q()` emit the RECOGNIZER direction of each `∃RO_0002158.ENSG` as
`RO_0002158(x,y) ∧ ENSG(y) → Q_i(x)` — a concept head (synthetic `Q_i`) with
the role in the body. Role-level relevance therefore (correctly, for its own
over-approximation) flags RO_0002158. The inverse pair IS correctly inert.

**What's needed for the giants: CONCEPT-level relevance.** The synthetic `Q_i =
∃RO_0002158.ENSG` are almost certainly inert (produced by the recognizer, never
consumed by a NAMED-class subsumption), so the symmetry adds no named
subsumption and elc (which, like ELK, drops symmetry) would be complete. To
route safely we must close relevance over CONCEPTS: a concept is relevant iff
named or feeding a relevant concept; a role is relevant iff in a body with a
relevant-concept head. This is delicate (must account for the generator
direction `Q_i(x)→∃R`, nominals, every rule) — silent incompleteness if wrong.
Deferred as deep work. The role-relevance code is the foundation.

ELK gets these giants by dropping the unsupported symmetric axiom; the answer
matches because the symmetry is inert for named subsumptions here.

**2026-06-11 update — 16744 is a VALIDATED +1, recoverable in principle.**
Experiment (KM_FORCE_INERT build forcing all sym/inverse inert -> elc): elc
classifies 16744 in ~110s, sig BYTE-IDENTICAL to the Konclude gold (consistent,
ZERO named subsumptions, the answer is empty). So dropping symmetry IS complete
for 16744. 8737 still times out in elc even forced (harder; ~743MB clauses).

Landed `ef8500a`: rewrote `concept_relevant_roles` as a BACKWARD slice from
named-concept / eq / empty-head goals (cleaner than the forward over-approx,
sound, 0 regression on the full sweep 5589: 562 ok, 552/6/4/0). BUT it still
does NOT route 16744 to elc, because the existential filler ENSG is NAMED, so
the generator `Q_0(x) -> ENSG(f(x))` has a named head on the SUCCESSOR term
f(x); the slice treats that as a goal, pulls Q_0 in, then the recognizer
`RO_0002158(x,y), ENSG(y) -> Q_0(x)` pulls RO_0002158 into the slice.

**2026-06-11 LANDED (commit `72acb3a`): 16744 recovered, +1 passrate (562->563
ok).** Implemented the successor-aware fix below as a one-line refinement of the
backward slice: exclude `Term::Fun(..)` named-concept heads from goal seeding (a
named concept on a Skolem successor f(x) is an existential filler, not a
subsumption goal; already-needed concepts still re-activate on any term). This
stops the existential RECOGNIZER from being pulled into the slice, so RO_0002158
is no longer marked relevant and the inert symmetric role is pruned -> 16744
routes to elc, classifies in 163s, byte-identical empty classification vs the
Konclude gold. Soundness vs gold UNCHANGED (sweep 5621: 553 agree / 6 incomplete
/ 4 unsound / 0 both-disagree; agree +1 only from the recovered ont). **8737
STILL times out** -- it routes to elc now too but elc itself times out at 240s
(~743MB clauses, the harder giant). 8737 needs elc scaling, not routing.

**2026-06-11 LANDED (commit `cd60ce3`): 8737 RECOVERED too — all three giants
now ok.** Clone-free EL completion hot loop (`in_edges` as flat
`Vec<Vec<(parent,role)>>`, index-loop NF4 rules, reused conclusion buffer;
schedule-only, no Lean re-cert needed). 8737 classify 252→221s standalone;
**in sweep 5690 it is ok at 205.7s wall, 9.5 GB peak, sig byte-identical to
gold**. Sweep 5690 total: 564 ok / 26 timeout / 1 memout; soundness 554/6/4/0
(agree +1 from 8737, no regression). Standalone elc timing on a slow node
showed 245s — node variance; the pipeline number is the real one. Parallel EL
completion is NOT needed for ORE anymore.

**(superseded by the LANDED note above) To recover 16744: successor-aware relevance.** A named
concept B(t) is a primary query goal ONLY when t is the CENTRAL term x
(subsumptions test B(x)); a named concept on a successor f(x) is a goal only if
it can propagate BACK to x. The reverse edges a symmetric R adds produce
concepts on SUCCESSORS; they reach a central named subsumption only through a
"downward"/target-producing reading of R -- a universal `..R(x,y)->E(y)`, a
range `R(x,y)->D(y)`, or domain/sub-role feeding such. The existential
RECOGNIZER `R(x,y),C(y)->Q(x)` produces on the SOURCE x and does not, so it must
be excluded from "reads R". Sound condition: a sym/inverse role is inert iff it
has no target-producing reading (no forall/range/domain) and isn't a sub-role of
one. DELICATE -- getting it wrong = silent incompleteness; wants careful proof
(ideally Lean). Deferred, but it is the concrete path to 16744 (+1).

Related: [[project_km_central_strategy]], [[project_km_rust_elc]], [[project_km_disjunction_blowup]].
