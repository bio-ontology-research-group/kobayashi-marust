---
name: project-km-bridge-nondeterminism
description: konclude_ht bridge order-dependent closure — root causes found 2026-07-06: dropped link-install reapply iterator, unregistered ATMOST reapply, merge label-union NEVER PORTED (u15 phase 4/5 deferred), blocking-off probe 20/20 deterministic; fixes in flight
metadata:
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

2026-07-06 (evening). Diagnosis of the bridge's nondeterministic
incompleteness went from "re-drive count-break" (earlier note, partially
wrong) to CONCRETE port gaps. Probe: `LateralMeniscus ⊑ Anonymous-51`
(ore_ont_1016, gold: holds) flips pairwise=true/false ~50/50 over 30 runs,
or_backtracks=0 both ways — the DETERMINISTIC part of the completion is
order-dependent.

**Confirmed root causes (all found by diffing against Konclude cpp):**
1. `ht_install_role_successor_edge` (u08) filled the reapply iterator from
   `node_install_individual_link` and DROPPED it — armed ∀/≤n restrictions
   never re-fired on late links. FIXED: consumes via the already-ported
   `apply_reapply_queue_concepts_restricted` (u10:574) for the link role +
   non-inverted indirect super-roles on source + inverted on destination
   (Konclude installs one link PER super-role; port resolves at lookup, so
   consumption must cover the same queues).
2. `apply_atmost_rule` (u08) never registered in the role reapply queue
   (Konclude cpp 15001-15005 does). FIXED: static role-reapply descriptor,
   applyALLRule pattern, guarded by is_concept_reapplied.
3. **`merge_individual_node_into` (u15) phase 4 (concept label-set UNION)
   and phase 5 (link relocation) are DEFERRED COMMENTS — never implemented.**
   The functional-role ≤1 merge drops the merged node's entire label, so
   the clash from unioning conflicting successors only fires if qualifiers
   landed on one node at creation = creation-order luck. THE deepest cause.
   Helpers all exist: create_merged_concept_dependency (u12:422), label
   iterators, add_concept_to_individual (u36:475). Konclude semantics:
   union skips tags contained ANY-polarity (containsConcept(c, nullptr));
   polarity clashes are caught by isIndividualNodesMergeable →
   isLabelConceptClashSet PRE-test (cpp 20714) — port's
   ht_individuals_mergeable only checks distinct-hash, must add the label
   clash-set test. Phase 5: port maintains NO connection-successor sets, so
   relocation must be done ATMOST-scoped or scans must FILTER purged/merged
   nodes (ht_role_successors_with_concepts has no purge filter).
4. Fixes 1+2 alone did NOT stop the flip (17/13 over 30) — expected, merge
   still broken.

**Blocking implicated then measured:** KM_BRIDGE_NO_BLOCKING (diagnostic
knob in bridge.rs configure_default_blocking): 20/20 pairwise=true — with
blocking OFF the clash is ALWAYS found. False runs end with ~103
DIRECTBLOCKED nodes; first invariant sweep said all violate blocked ⊆
blocker, but that sweep walked RAW arena slots (localization keeps stale
node copies) — re-measuring with the id→current-node vector walk. The
blocking test itself (is_label_concept_optimized_blocking u19:173, B1 full
subset + B2 inverse) and the retest chain (propagate_individual_node_modified
→ blocking-update review queue → probe 29) all look faithfully ported;
suspicion is the invalid-block state is DOWNSTREAM of the broken merge
(dropped labels → wrong subset relations early, blocked nodes park before
labels grow back through reapply).

**Working setup:** probes on ws via /tmp/probe12.sh (12x
KM_BRIDGE_TRACE=1 bridge_probe_pair + per-run /tmp/btrace_N.txt);
KM_BRIDGE_TRACE dumps per-pass inserts/backtracks/nodes + root label +
blocked-node subset-invariant sweep in bridged_unsat.

**FULL MECHANISM IDENTIFIED (evening, via clash-descriptor + FINDTAG
tracing):** the flip is `Anonymous-51 ∧ ¬Anonymous-51` on the ROOT.
Derivation chain: root needs Q_623 via the recognition-across-edge clause
`Q_624(y) ∧ R48(x,y) → Q_623(x)`, bridge-encoded as `Q_624 ⊑ ∀R48⁻.Q_623`
(absorbed on the successor side). With functional roles the root's
R-successors MERGE — and merge phase 5 (incoming-link relocation) was
never ported, so the root LOSES its edge to the merge target: the ∀R⁻
recognition fires on the target but its ancestor link points at the OTHER
parent, so Q_623 never reaches the root. Which sibling becomes the merge
target is hash-order — hence the 50/50 flip. After phase 4 + resolved-
contains fixes: false runs converge to ONE stable 467-node fixpoint,
0 blocked-subset violations, single-pass closure (reapply works); true
runs clash at ~20 nodes. Konclude's phase 5 relocates ONLY the tree
predecessor's links (children are pruned + re-derived from the unioned
label; the connSuccSet arm conditions reduce to nominal/ancestor cases).

**Fix in test (probe30):** `ht_relocate_incoming_links` (u15) — per-link
createMERGEDLINKDependency + ht_install_role_successor_edge (fires reapply
= Konclude's `…Reapplyed`); called ancestor-scoped in merge phase 5 +
parent-scoped in ht_apply_atmost_merge. Old links stay in hashes — the
ghost filter in ht_role_successor_links realises removeIndividualLink.
Also un-deferred: u36 insert-clash now builds the faithful two-concept
clash chain (was a bare Dependency descriptor — made clash tracing
possible). Trace/diag knobs in bridge.rs: KM_BRIDGE_TRACE (per-pass +
clash descriptors + blocked-subset invariant sweep), KM_BRIDGE_FIND_TAG,
KM_BRIDGE_DUMP_NAMES, KM_BRIDGE_NO_BLOCKING.

**Round 2 (still 13-17/30 flipping, all fixes tests-green 1208):** false
run root has GenericBodyStructure+Q_266+¬Anonymous-51 but NO Q_623 (tag
542); Q_623/Q_708/Anonymous-51 derive fine on OTHER nodes (3, 28, 29). The
missing hop = `Q_624(y) ∧ R48(x=root,y)` → `∀R48⁻.Q_623` never reaching
the root. Fixes added (each correct, none closed it): edge-restricted ∀
branch in apply_all_rule (cpp 16306-16345, uses the LIVE
get_link_processing_restriction u03:933 — the u09 "todo" comment was
stale); conn-successor-set maintenance in ht_install_role_successor_edge
(cpp 22346-49) + all-predecessors inverse arm in ht_all_rule_targets (was
ancestor-only); direct inverse-role queue consumption on destination at
link install (bridge wires set_inverse_role but NOT inverse super-role
lists). NAME-TAGs: Q_623=542 Q_708=2960 GenericBodyStructure=2438
Q_624=543 Q_266=277 BodyPart=2436 atLeastPaired=278 Q_622=2844
Anonymous-51=2961; role tags 100+i (R48=148, R5=105).

**Diagnosis toolkit (bridge.rs, all env-gated):** KM_BRIDGE_TRACE
(per-pass inserts/backtracks/nodes, typed clash descriptors, blocked ⊆
blocker invariant sweep), KM_BRIDGE_FIND_TAG=t1,t2 (which current nodes
carry tags + blocking flags), KM_BRIDGE_DUMP_EDGES=indi,.. (outgoing edges
+ ghost status), KM_BRIDGE_DUMP_NAMES (clause dump by name + NAME-TAG
resolution), KM_BRIDGE_NO_BLOCKING. ws scripts: /tmp/probe30.sh (build +
konclude_ht tests + 30x determinism tally), /tmp/findtag2.sh.

**RESOLVED — 30/30 deterministic (probe30, 1208 tests green).** The final
mechanism: root's R48-successors (nodes 4, 12) were DIRECTBLOCKED before
deriving Q_624; their blockers DID derive Q_624 → armed ∀R48⁻.Q_623 —
the B2 blocking condition must then invalidate the block (blocker's ∀R⁻
fires backward over the parent edge in the unraveling; Q_623 ∉ L(root)),
but the port's B2 walks the BLOCKED NODE'S OWN successor hash for edges
to the parent — and the port never installed the INVERSE-direction link
Konclude creates on the destination (cpp 22300–22341 roleLinkerIt inverse
arm). B2 was VACUOUS → unsound blocks, order decided whether the clash
region was built before the block formed. **THE fix: mirror inverse
install in ht_install_role_successor_edge** — destination --inv(R)-->
source registered in destination's hashes (creator = ∃-applier), its
reapply queue consumed over the new link, source's conn-set records the
destination. B2 now sees the parent edge; ∀R⁻ fires as plain forward ∀
over the inverse link.

**Full fix list of the arc (all konclude_ht, tests-green):** link-install
reapply consumption + super-role queues (u08); ATMOST static reapply
registration (u08); merge phase 4 label union + phase 5 ancestor-scoped
relocation ht_relocate_incoming_links (u15); isLabelConceptClashSet
mergeable pre-test (u08); 4x has_concept-stub→resolved-contains
migrations (u05/u08/u09 — raw/tag collisions skipped required adds);
merged/purged ghost filter in ht_role_successor_links (u08); faithful
two-concept insert-clash chain (u36); edge-restricted ∀ branch in
apply_all_rule (u09, cpp 16306-16345); conn-successor-set maintenance at
install + all-predecessors inverse arm in ht_all_rule_targets (u10);
mirror inverse install (u08) = the decisive one.

**COMMITTED 5099d52 (pushed).** bridge_classify_full 1016 x3 IDENTICAL:
derived=32712 gold=32739 missing=27 spurious=0 nondet=0 ~51s. Determinism
arc DONE.

**Residual 27 missing (deterministic, ONE recognition family):** all in
the Q_506 / Anonymous-324 / IntrinsicallyPathologicalBodyProcess /
Anonymous-351 cluster. Chain: `IneffectiveCardiacFunction ⊑ Anonymous-324`
needs Q_506 (Q_506→Anonymous-324); Q_506 recognized by the CONJUNCTIVE
two-trigger clause `BodyProcess ∧ Q_162 → Q_506`, reached through multi-hop
∃-successor recognitions (Q_505→∃R23.Q_506, Q_506∧R23→Q_505;
Q_528→∃R27.Q_506, Q_506∧R27→Q_528). So the node must derive BOTH BodyProcess
AND Q_162 via a chain of ∃R23/R27 hops + backward recognition. Not the
order-dependence — a genuine deeper-recognition / v1-fragment-coverage gap.
Hypotheses to test next: (a) two-trigger absorption — bridge hangs the impl
off ONE trigger's CCSUB; verify the AND-rule unfold with the 2nd trigger as
a residual ¬-literal actually fires when both land; (b) the ∃-successor
recognition needs another reapply pass the global-fixpoint break may cut
(re-check with the now-correct reapply). Diagnostic ready:
KM_BRIDGE_DUMP_NAMES resolves NAME-TAGs (Q_506, Anonymous-324=2871,
IntrinsicallyPathologicalBodyProcess=3469), KM_BRIDGE_FIND_TAG traces which
node holds each hop.

**Completeness gap DIAGNOSED (post-commit):** all 27 missing are ONE GALEN
recognition cluster (Q_506/Anonymous-324/IntrinsicallyPathologicalBody
Process/Anonymous-349). Root pair `Anonymous-349 ⊑ IntrinsicallyPath` is
pairwise=FALSE too (not a read-off limit — a real saturation miss);
unsupported=0 (all clauses encoded). The multi-trigger implication rule
(u09 apply_implication_rule) IS correct + complete node-locally: scans
triggers, installs con_des on the FIRST missing trigger's per-concept
condensed reapply queue (add_concept_to_reapply_queue_concept, keyed by
concept tag + negation=!trigger.negated), re-fires when it lands
(insert_concepts_to_individual_concept_set fills reapply_it via
node_concept_reapply_iterator_by_tag(tag,neg) → drained by
apply_reapply_queue_concepts_condensed_iterator; polarities MATCH). So the
gap is NOT node-local multi-trigger order. It is a DEEPER recognition:
node {Anonymous-349} has {Anonymous-349, Q_23 (asserted), Q_674} but must
derive BodyProcess+Q_162 (for Q_506) via GALEN definer chains
(`BodyProcess∧Q_170∧Q_675→Q_674`, `pathological∧R11(0,1)→Q_23` = successor
recognition, `Q_505→∃R23.Q_506` / `Q_506∧R23→Q_505`). Needs the built
successor model + inverse-recognition to converge — the SAME hard class as
the 8 timeout onts.

**ROOT-CAUSED via FIND_TAG on the pairwise {Anonymous-349,¬IntrinsicallyPath}
saturation:** root (indi=0) DERIVES BodyProcess(184), Q_170(195), Q_675(579)
→ correctly yields Q_674(2915) — SO THE MULTI-TRIGGER IMPLICATION RULE WORKS
(3-way conjunctive recognition fires). Root is MISSING Q_162(182) and thus
Q_506(458)=BodyProcess∧Q_162. Q_162 is NOT node-locally derivable from
{Anonymous-349}; it comes only from the ∃-successor recognition family
(Q_505→∃R23.Q_506, Q_506∧R23(0,1)→Q_505; Q_528→∃R27.Q_506, Q_506∧R27→Q_528).
So the 27-gap is NOT a rule bug — it is DEEP SUCCESSOR-MODEL RECOGNITION:
build the ∃R23/∃R27 successor, recognize Q_506 there, inverse-propagate
back. Same mechanism the 8 timeout onts need. Genuinely multi-session (the
successor-signature caching + lazy ∀-extension Konclude uses). NOT a quick
fix; do not chase it as a completeness patch.

**STRATEGIC (for beat-Konclude goal):** the bridge is TEST-ONLY, addresses
only the 8 timeouts (8/587). The DOMINANT goal gap by count is the SPEED
gap on ~258 ALREADY-SOLVED onts (km correct but slower than Konclude) — the
bridge does nothing for those. See [[project_km_beat_konclude_gap]]: after
in-process elc WIN=318/576 (55%); the other ~258 need CB/HT throughput, not
the HT port. Recommend: decide whether to keep pushing konclude_ht
completeness (deep, 8-ont ceiling) vs attack the speed gap (broad, ~258
onts). Then: wire the bridge toward the 8 timeout onts
(541/3215/7914/9663/9724/12653/14817+10621). Related:
[[project-km-role-automata-port]], [[project_km_beat_konclude_gap]].
