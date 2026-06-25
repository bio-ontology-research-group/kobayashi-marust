# Lever C — faithful Konclude G2/G3 saturation port (throughput giants)

Status: source-grounded plan (2026-06-25). PORT from Konclude, do not invent
([[feedback_port_from_konclude]]). This REPLACES an earlier draft that invented a
"successor-subtree cache" — Konclude does NOT do that; the real mechanism is below.

## What Konclude actually does (read from source, file:line)

`Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp`:

- **Shared non-branching saturation**, one node per (concept, polarity); `∃R.C`
  reuses the shared C-node (this IS Konclude's amortization / "cache" — there is no
  separate subtree cache).
- **∀-rule = CHECK, never pollute** (`isCriticalALLConceptDescriptorInsufficient`,
  :3451). For a `∀R.C` descriptor on node `n`, walk `n`'s R-successors; for each
  successor read its `ReapplyConceptSaturationLabelSet` and test
  `succConSet->containsConcept(operand, neg)` for every operand of C (:3514-3518). It
  does NOT add C to the successor. If an operand is absent ⇒ `return true` (critical).
- **Critical ⇒ INSUFFICIENT + propagate by STATUS FLAG, not label** (:881-884):
  `updateDirectAddingIndividualStatusFlags(n, INDSATFLAGINSUFFICIENT)` +
  `INDSATFLAGPROPAGATIONINCOMPLETE` + `setInsufficientNodeOccured`. Insufficiency
  rides up the predecessor chain via `updateIndirectAddingIndividualStatusFlags(n,
  succ->getIndirectStatusFlags())` (:1657/1803/1939/2018) — G2: a node inherits its
  successor's STATUS flags, never its concept set.
- **3-state outcome**: CLEAN (completed, no clash, not insufficient) ⇒ read subsumers
  off the node; CLASHED ⇒ unsat; INSUFFICIENT ⇒ residue → complete tableau.
- Cache key for the per-concept result is **(concept, negation)** (KONCLUDE-SATURATION-
  CACHE-SPEC.md), reused at every occurrence. Session 6g: that key is INERT in KM
  (KM's shared pass already shares C-nodes; each (concept,neg) saturates once/run).

## What KM already has (do NOT re-invent)

- Shared pass: `saturate_global` (`hypertableau.rs:3366`), one node per concept via
  `concept_node_of` — = Konclude's shared saturation.
- The G2/G3 CHECK: `KM_HT_QO_KPSET` — `kp_check_head` containment-checks a head write
  instead of writing it; misses set `kp_insufficient`; `kp_finalize` =
  `checkCriticalIndividuals`. This IS `isCriticalALLConceptDescriptorInsufficient`.
- Criticality at the ∀-write: `apply_head` t!=X branch (`:4310-4346`) already marks
  `qo_insufficient` + records `kp_insuff_nodes` when a write is not "clean".
- Per-node CLEAN split + reverse-reachability affected-set (`card_defer`).

## The REAL gap (why KM over-defers, and the faithful fix)

KM's kpset/criticality is present but **too coarse on inverse-heavy giants**: every
inverse-bridge back-edge write is a "miss" (7581: kp_miss≈930k; 9724: 66M), so
`qo_insufficient` trips globally and the per-node reverse-reach marks ~every concept
insufficient (7581: 0/72989 clean) ⇒ whole classification deferred ⇒ falls to the slow
per-concept path. The faithful port is NOT a new cache; it is making the G2/G3
propagation **precise** so CLEAN concepts survive:

1. **Status-flag (not label) propagation, edge-direction-correct.** Port Konclude's
   `updateIndirectAddingIndividualStatusFlags`: insufficiency propagates ONLY along the
   genuine forward predecessor chain of the node that is actually critical, not via the
   conflated reversed inverse back-edges. KM's reverse-reach currently follows inverse
   back-edges too ⇒ over-marks. Restrict propagation to Konclude's predecessor links.
2. **Per-creation-role ALL-concept extension** (`getRoleSuccessorALLConceptExtensionData`,
   :960; `CSaturationLinkedSuccessorIndividualALLConceptsExtensionData`): the ∀-operands
   live in a SEPARATE per-(successor,creation-role) structure used only for the
   criticality check + consistency, NOT in the shared subsumer label. KM writes them
   into the label (pollution) or defers; port the separate extension so the shared
   subsumer label stays clean and only criticality consults the operands.
3. **Backward propagation to predecessors** (`addConceptFilteredToIndividual` on the
   ancestor, :1235): the sound named-subsumer inverse contribution goes BACKWARD to the
   predecessor (non-critical), distinct from the forward operand check. KM conflates
   these via reversed-edge label reads.

Together these keep the shared single pass sound for ∀ + inverse WITHOUT ×concepts
memory and WITHOUT global deferral — Konclude's actual lever. This is the substantial
multi-session engine work (matches the shiq_build "orders of magnitude" finding).

## Build plan (incremental, ws synthetic-test-first, Lean re-cert at END)

1. Regression test locking the CLEAN/INSUFFICIENT verdicts KPSET already produces on a
   tiny ∀+∃+inverse KB (the safety net).
2. Port #1: restrict insufficiency propagation to forward predecessor links (not
   inverse back-edges) — measure 7581/9724 clean% rises from ~0.
3. Port #2: the per-creation-role ALL-concept extension (operands out of the subsumer
   label) — eliminates the remaining pollution-driven misses.
4. Measure on 7914/9724 isolated (`km tableau` on a dumped TIN, group-safe). Target:
   global pass certifies most concepts; small residue to the verify funnel.
5. Full corpus sweep (rare, unimatrix) + Lean re-cert of the affected QoSat rules.

Konclude anchors: isCriticalALL :3451, status-flag propagation :1657/1803/1939/2018,
INDSATFLAGINSUFFICIENT :881-884, per-creation-role ext :960, backward write :1235.
KM anchors: kp_check_head / kp_finalize, qo_insufficient `apply_head:4331`,
kp_insuff_nodes reverse-reach, saturate_global :3366.
