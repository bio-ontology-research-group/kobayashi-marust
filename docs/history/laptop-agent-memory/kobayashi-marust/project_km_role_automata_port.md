---
name: project-km-role-automata-port
description: 2026-07-05 role-chain automata port (14817) — consuming side ALREADY in konclude_ht (u05 automat rules); porting CRoleChainAutomataTransformationPreProcess is the missing producer; full algorithm map in task
metadata: 
  node_type: memory
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

2026-07-05: user directed the role-automaton port for 14817 as a FULL Konclude
port, reusing the konclude_ht effort.

**Reuse finding (the big one):** konclude_ht ALREADY has the consuming side
live + tested — `apply_automat_choose_rule` / `apply_neg_automat_choose_rule`
(completion/u05.rs), CCAQAND/CCAQCHOOCE dispatch (u03.rs:443/467/605), opcodes
CCAQCHOOCE=10 CCAQALL=11 CCAQSOME=-11 CCAQAND=12 (model/op.rs:65-72),
DepKind::AutomatChoose (u28.rs). Model has CRole.is_complex_role +
(indirect)super linkers + role_chain_super/sub_sharing_linker. MISSING pieces:
(1) CRoleChain is a stub (model/stubs.rs) — needs real
{role_chain_linker: Vec<RoleId>, inverse_role_chain_linker}; (2) the
preprocessor itself (source: laptop
Public/software/Konclude/Source/Reasoner/Preprocess/
CRoleChainAutomataTransformationPreProcess.{h,cpp}, 252+1539 lines, FULLY READ;
still carries my June KTRACE instrumentation on ws:~/konclude-build).
classifier/mod.rs:5657 marks it as the port boundary.

**Complete algorithm map lives in task #8's description** (10 numbered steps
with cpp line refs: collectSubRoleChains, createMissingInverseChainedRoles,
createInverseRoleChainLinkers, transformVALUERestrictions,
createDomainRangePropagations, createRecursiveTraversalData,
transformFORALLPropagations, convertAutomatConcept, the 3
generateRoleChainAutomatConcept overloads incl. the transStart/transEnd loop
wiring that encodes transitivity, helpers). Read task #8 before coding.

**PROGRESS 2026-07-05 late: (a)+(b) DONE — full preprocessor surface ported
across 6 commits (2810f4b 726db9f c1f4487 0fc1759 1e0fadf 5dc97e7).**
engine/src/konclude_ht/preprocess/role_chain_automata.rs holds the complete
port incl. preprocess()/continuePreprocessing drivers. Fidelity notes: QHash
multi-value order mirrored by Vec reversal; C++ precedence quirk
opNeg^(conNeg==negated) in hasPropagationConcept kept as written (dedup-only).

**MILESTONE 2026-07-05 night (6a7a67e): AUTOMATON LIVE END-TO-END, (c) DONE.**
u05 apply_automat_transactions ported for real — the old blocker was STALE
(ht_all_rule_targets/u10 is the port surface for successor iteration, not the
pn3 iterator stub). u08 ht_reapply_universal_restrictions extended: hierarchy-
resolved role match + AQAND/AQALL state-graph walk so new edges re-fire
automaton states (stands in for the reapply queue). 15 synthetic tests in
preprocess/automata_test.rs: structure (ε-loop, chain gluing, transStart/End,
∃-duality, hasValue rewrite, dom/range prop incl. the CORRECT transitive skip
via hasPropagatedConcept) + e2e through run_completion_on (transitivity 2-hop
clash, subrole-into-transitive, chain ORDER sensitivity both ways, the 14817
part_of shape, preexisting-successor walk). **1390/1390 tests green.**
Gotchas: conf_specialized_automate_rules must be true (default false);
indirect_super_roles includes the role ITSELF (positive, first) per
CSubroleTransformationPreProcess; complex marking propagates to all indirect
supers; dom/range prop concepts are created BEFORE the ∀ pass so they get
automaton-converted too; role tag 1 = TOP-role sentinel.
REMAINING: (d) production route for 14817 — mirror the validated
transformation over KM's fast-Ht clause encoding (ofn/cb_to_ht, states +
transitions as DL-clauses) or konclude_ht classify from orchestrate (far).

**2026-07-06 (1e4b9a2): the production-route FOUNDATION landed —
konclude_ht/bridge.rs** (TInput→OntologyArenas + tri-state probe driver,
4 e2e tests through ofn→convert→bridge→run_completion_on; 1397 green).
Key findings for the next bridge waves: (1) GCIs must ride the TOP concept
(CCTOP → AND rule; create_new_individual labels successors with TOP) or
successors never see the TBox; (2) cb_to_ht's definer RECOGNITION clauses
(B(y)∧R(x,y)→Q(x)) CANNOT be encoded trigger-less (covering disjunction →
unbounded successor chains, 454k nodes) — they need Konclude's absorption
wave; (3) probe isolation requires per-task databox COW (unported) — v1
rebuilds ctx per probe; (4) a STOP verdict must stay UNKNOWN (tri-state),
never folded into unsat/sat. Next waves toward production classify:
absorption (kills the recognition-clause gap + the per-node covering ORs),
inverse wiring in the bridge, then the automata preprocess plugged into
bridged roles for 14817.

**7d685d8**: role hierarchy R⊑S in the bridge (transitively-closed
indirect_super_role_linker install, e2e test via ofn) + TInput.inverse
counts unsupported. **0024565**: KM_BRIDGE_ONT coverage diagnostic.
**cff7cc7**: the absorption-shape RECOGNITION clauses (D(y)∧R(x,y)→E(x))
now encode as D ⊑ ∀R⁻.E over always-wired inverse roles — coverage on
ore_ont_1016 jumped 85% → 95.8% (unsupported 1636 → 150); e2e test
bridge_exists_recognition_inverse proves ∃R.B⊑Q flows through the inverse
edge. Remaining 150 = multi-role-body + ⊤-edge clauses (note: same count
as the elc-cert "150 residual clauses" on 1016 — likely the same non-EL
residue). **1660dda scale probe MEASURED on 1016** (bridge_scale_probe, KM_BRIDGE_ONT
+ KM_BRIDGE_PROBES): bridge build 5-7ms; easy concepts 10-11ms/probe
correct-sat 1 node; successor-rich Abdomen = STOP at 2114ms/388 nodes —
EXACTLY 388×13k impls = the 5M drive cap. Diagnosis: absent-trigger CCIMPLs
are re-queued per node instead of REGISTERED. **THE measured scale blocker
= the condensed reapply queue port (addConceptToReapplyQueue, u09
install-to-trigger W3-DEFER)**; consuming side (label-set queue heads +
apply_reapply_queue_concepts_condensed_iterator) already ported. **10ecc9f: install-to-trigger WIRED** — apply_implication_rule's absent-
trigger branch now registers via the u10-ported add_concept_to_reapply_
queue_concept (GOTCHA: the addConceptToReapplyQueue overloads were ALREADY
ported in u10 — check u10 before porting node-level helpers). 1399 green.
Abdomen probe STILL stops at 388 nodes: the cap is each node's FIRST scan
of 13k TOP-attached impls (388×13k=5M), NOT re-processing.

**SCALE UNLOCK LANDED (2 commits, 1016 now CONVERGES):**
- **3a1b0f3 absorption wiring**: an impl with a positive concept trigger
  attaches as an operand of that trigger's CCATOM concept, promoting it
  CCATOM→CCSUB (positive CCSUB dispatches to the AND rule; negated CCSUB is
  atomaric — already ported in stubs.rs/u03). A node then unfolds ONLY the
  impls whose trigger is in its label — node-count-independent, Konclude's
  absorption mechanism. All 13018 encoded impls on 1016 absorb (top=0).
  Sound+complete: trigger-free node ⇒ clause vacuous (positive DL-clause
  bodies). Made per-node work FLAT: Abdomen 388→115730 nodes same walltime.
- **ebcf41c enable default blocking**: absorption exposed the REAL blocker —
  every blocking-search flag defaulted FALSE, so get_blocking_individual_node
  always returned NONE and successor trees never blocked. Added
  configure_default_blocking() (Konclude ctor 115-118/157 + u31 default:
  optimized_sub_set + anywhere_linked_candidate_hash + lazy_exact_hashing +
  save_core_blocking_concepts_candidates coupling cpp 741). RESULT: all 50
  named probes on 1016 converge Some(false) in 7-28ms, max 247 nodes;
  Abdomen 3231ms/388-node-STOP → 13ms/51-node-SAT; 50-probe sweep 0.95s.
  1399 green. **The konclude_ht production route now scales on a real ORE
  ontology.**

**VERDICT CORRECTNESS PROVEN (bcd1ccf):** bridge_correctness_sample
(ignored diagnostic) reads a km-classify gold JSON and, per sampled named
subject, checks every gold super (bridge must derive it) + equal count of
gold-known non-supers (must not). GOTCHA: draw negatives ONLY from the
gold universe — cb_to_ht mints internal DEFINER concepts (Q_NNNN, not
named classes) that gold never lists as supers; a subject subsumed by a
definer is correct, sampling it as a negative gives false "unsound". On
ore_ont_1016, 150 subjects: pos_checked=1584 missing=0, neg_checked=1584
spurious=0 — the bridged konclude_ht route is SOUND + COMPLETE on this
real-ORE sample (unsupported=150 multi-role clauses don't touch these
subs). Gold from `./target/release/km classify /tmp/ore_ont_1016.owl`.

NEXT (toward production classify + beat-Konclude): (a) MODEL READ-OFF
classify — 1016 probes all backtrack=0 (effectively Horn here), so
saturating {A} once and reading the root label's named tags gives A's
subsumers in O(concepts) saturations, NOT O(concepts²) pairwise probes
(naive pairwise = 2500²×15ms = 25h, infeasible; Konclude does 1016 in
0.38s). Build read-off classify, validate FULL sub-set vs gold. (b) reuse
terminology across concepts (per-task databox COW / reset process ctx keep
ontology arenas) — kill the per-probe rebuild. (c) multi-role-body shapes
(150 residual). (d) automata into bridged roles (14817). Then orchestrate
wiring + IBEX head-to-head.

Note: transformVALUERestrictions (hasValue on complex role → ∃R.{o}) is
Konclude's counterpart of the [[project-km-10702-nomlink-fix]] — consistent
with that fix's semantics.
