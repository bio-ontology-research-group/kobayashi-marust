---
name: project_km_konclude_study
description: "Source study of Konclude (2026-06-18) — how it solves KM's hard onts; the 4 mechanisms + prioritised KM integration plan"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

2026-06-18: Read Konclude C++ source (cloned /tmp/Konclude) with 4 parallel agents to
learn how it solves KM's residuals (live ∀+⊔ family 5303/10702/1603; central blowup
9663/4604/11460; context explosion; near-Horn 7246/7581). Writeup: **docs/KONCLUDE-STUDY.md**.
Raw notes: /tmp/konclude-findings-{saturation,classification,tableau,absorption}.md.

**Core finding:** KM ships TWO *complete* reasoners (CB engine = complete CB disjunctive
saturation; HT = complete hypertableau) and runs one over the WHOLE ontology. Konclude is
**lazy**: an *incomplete non-branching* saturation decides ~95% of concepts, complete
tableau runs only on the residue. KM's CB engine blows up on ∀+⊔ *because* it is complete
(materialises all incomparable disjunctive contexts); Konclude never splits in saturation.

**KM already owns the hard pieces** — gaps are granularity/wiring not missing algorithms:
- `elc` (elcomplete.rs) = the non-branching saturation core, but bails None on disjunctive
  head (elcomplete.rs:298).
- canonical-model certificate `cert_round` (elcomplete.rs:856+) = the residue check, but
  WHOLE-ONTOLOGY all-or-nothing, not per-concept.
- HT (tableau.rs) already has backjumping(DepSet)+disjunction learning+anywhere blocking+
  VSIDS(KM_TAB_*)+pseudo-model cache for BLOCKING(task35)+QuasiOrder(task62).

**Konclude's 4 mechanisms** (file refs in docs):
1. Saturation residue filter: one shared node/(concept,polarity), ∃ reuses shared filler
   node (graph O(#concepts)), ∀ backward-only, OR never splits → 3-state CLASHED/CLEAN/
   INSUFFICIENT; only INSUFFICIENT gets a real test. applyORRule cpp:6021; common-disjunct
   rule A⊑X∧B⊑X⟹A⊔B⊑X.
2. KPSet classification: known/possible subsumers; **pseudo-model merge** refutes A⋢B with
   a linear label+cardinality walk (the antidote to KM-HT's ~196k backtracks/concept);
   transitive confirm-down/refute-up; only residue → tableau. Stats line cpp:2689 splits
   n(n-1) into told+derivation+pruned+pseudomodel+calculated.
3. Triggered-implication absorption (CTriggeredImplicationBinaryAbsorberPreProcess): global
   ⊤⊑¬C⊔E → dormant trigger(C):C→E (fires only where C appears) = direct fix for KM's
   pred_lteq root-context blowup. + common-disjunct hoist + disjunct sorting + nominal→ABox.
4. Per-test: resolution backjumping (cpp:7779), semantic branching+VSIDS, deterministic
   floor, anywhere blocking w/ 64-bit label sig, 3 caches (unsat trie superset / sat-expander
   exact / completion subset).

**Prioritised KM integration plan** (see docs for detail; relates to tasks #42/#52):
- **P1 (highest, mostly reuse, no re-cert for inc.1):** make elc+cert PER-CONCEPT 3-state
  filter — park disjunctions instead of bailing, route only INSUFFICIENT concepts to CB/HT.
  Inc.2 = common-disjunct extraction (1 small Lean ⊔-distribution lemma).
- **P2:** classification-level pseudo-model merge gate for HT path (refute non-subsumptions
  cheaply; refutation-only → no re-cert).
- **P3 (frontend):** trigger-keyed binary absorption (contrapositive move named neg disjunct
  to body) + common-disjunct hoist + disjunct sort; mostly fixpoint-preserving no re-cert.
- **P4:** sat-expander 64-bit signature cache + 2-stage unsat trie (monotone, no re-cert).
P1+P3 target ∀+⊔ & context-explosion; P1 alone helps central-blowup & near-Horn.
Optional: run deployed Konclude with classification stats on 5303/10702/1603 to confirm few
SAT tests survive before investing. Relates to [[project_km_disjunction_blowup]]
[[project_km_family_diagnosis]] [[project_km_rust_elc]] [[project_km_hermit_trace]].
