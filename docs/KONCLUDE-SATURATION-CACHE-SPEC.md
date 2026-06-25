# Konclude saturation caching / lazy completion — faithful port spec

Extracted (read-only) from `Konclude/Source/Reasoner/Kernel/` (mainly
CCalculationTableauCompletionTaskHandleAlgorithm.cpp + the approximation-saturation
task + CIndividualSaturationProcessNode*). Ground truth to PORT. See
[[feedback_port_from_konclude]]. Companion to the blocking + disjunction specs.

## The mechanism (Konclude's speed/laziness lever)
A deterministic, NON-branching SATURATION pass runs first, per concept; the full
branching TABLEAU runs only on the residue saturation can't decide.

3-STATE per concept (status flags on CIndividualSaturationProcessNode):
- `isCompleted()` + no clash + not insufficient ⇒ **SAT** (cache blocks all further work).
- `INDSATFLAGCLASHED` ⇒ **UNSAT** (reuse the clash decision).
- `INDSATFLAGINSUFFICIENT` ⇒ **UNKNOWN** → hand residue to the full tableau (which
  skips expansion of already-saturated concepts via PRFSATURATIONBLOCKINGCACHED).

CACHE KEY = **(concept, negation)** — content-addressed, NOT node-id. Stored on the
concept itself (CConceptSaturationReferenceLinkingData → per-negation →
CIndividualSaturationProcessNode). So one saturation of `∃R.C` is reused at EVERY
occurrence / every satisfiability test (subsumption, domain, etc.) — amortized.

REUSE SOUNDNESS (tryEstablishSaturationCaching 21670, validateSaturationCachingPossible
21862): reuse valid iff sat node `isCompleted()` (no omitted consequences) AND not
insufficient; and the completion node's added concepts are a SUBSET of the saturation
label (`satConSet.hasConcept(c, neg)` for every newly added c — else invalidate,
PRFSATURATIONBLOCKINGCACHEDINVALIDATED). Cardinality-problematic
(INDSATFLAGCARDINALITYPROBLEMATIC) ⇒ do NOT block successor creation (branching may
still be needed). Nominal-connection ⇒ only with reactivation support. Backend cache
(per-individual, 22582) is a secondary representative cache; orthogonal.

## Mapping to KM (what already exists vs the gap)
KM ALREADY HAS the saturation gate, heavily developed:
- **QoSat** (hypertableau.rs `saturate` 3170 / `saturate_global` 3235): the deterministic
  forward-only per-concept saturation. Recent commits (4697ddc/678198e/a02063d/c34120c)
  made the **forward-only per-concept QoSat gate** sound+complete on 7581 (verify funnel
  KM_HT_QO_VERIFY). This IS Konclude's saturation pass.
- **3-state / insufficient** ≈ KM's `kp_insuff_nodes` / `card_defer` / criticality
  (QoResult): a node is INSUFFICIENT when a ∀/cardinality/disjunction deferral is live →
  defer to the complete verify (= Konclude INDSATFLAGINSUFFICIENT → tableau residue).
- **Cross-query cache attempt** = KM_HT_SATCACHE3 (full-label NODE signatures pooled
  across queries) — found largely INERT (helps at most 3215, even there inert; the
  inverse-bound targets break its assumptions). NOTE this is keyed on NODE full-label
  signatures, NOT Konclude's (concept, negation) content key.

THE GENUINE GAP (the faithful port): a CONTENT-ADDRESSED cache keyed by **(concept, neg)**
(the QUERY concept, not a node signature) storing the QoSat 3-state result + saturated
label, reused across ALL per-concept satisfiability tests — i.e. Konclude's
per-concept-amortized cache, distinct from satcache3's per-node-signature pooling. With
the soundness conditions: completed + not-insufficient ⇒ SAT-reusable; clashed ⇒
UNSAT-reusable; subset-validation on reuse.

## Open question before porting
KM's per-concept QoSat already RE-RUNS saturation per concept (no cross-concept reuse of
one concept's saturated label). The Konclude cache reuses concept C's saturation wherever
C occurs. BUT memory evidence (satcache3 inert; project_km_family_diagnosis "caching
~1% hit, subsumed by no-goods") suggests cross-concept reuse may be low-hit on the ORE
corpus because per-concept cores are context-specific. ⇒ VALIDATE the hit-rate
assumption on a target before a full port (cheap KM_HT_QO_TALLY-style probe), don't
assume it pays off. The decisive new-fidelity piece THIS session that targets a KNOWN bug
is the mode-5 blocking port (10908 false-UNSAT) — validate that first.
