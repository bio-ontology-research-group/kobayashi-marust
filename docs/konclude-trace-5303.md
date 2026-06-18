# Konclude vs KM on ore_ont_5303: where the path diverges

*2026-06-18T09:09:15Z by Showboat 0.6.1*
<!-- showboat-id: 1f2de799-a01c-4576-bd18-04b0383a76ab -->

Prerequisites (session-local): the Konclude source at `/tmp/Konclude` and KM's normalised clause set for ore_ont_5303 at `/tmp/c5303.json`. 5303 is the canonical live forall+or disjunction-family ontology KM times out on and Konclude solves in ~0.16s single-threaded. This document traces both engines on it from the actual source and pinpoints the divergence.

```bash
python3 /tmp/tr_struct.py
```

```output
clauses=937  disjunctions(head>=2)=38  clash(head=0)=40

The live disjunction family, as DL clauses (note each pair Qi/Qj also has Qi+Qj => bottom):
  T  =>  Q_6  v  DNA
  T  =>  Q_7  v  Q_5
  T  =>  Q_24  v  Q_22
  T  =>  Q_31  v  Q_30
  T  =>  Q_52  v  Q_51

The paired clash clauses that make those disjuncts complementary:
  Q_6  +  DNA  =>  bottom
  Q_7  +  Q_5  =>  bottom
  Q_8  +  Q_6  =>  bottom
  Q_24  +  Q_22  =>  bottom
  Q_23  +  Q_25  =>  bottom
```

## Konclude's path: one deterministic saturation pass, never branch

Konclude runs a single non-branching tableau saturation over the whole TBox (`CCalculationTableauApproximationSaturationTaskHandleAlgorithm`). It keeps **one shared node per (concept, polarity)** — existential successors reuse the filler concept's node, so the graph is bounded by the number of concepts, not by model size. The disjunction rule is the crux: it is **parked, never split**.

```bash
sed -n '6021,6034p' /tmp/Konclude/Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp | sed 's/\t/  /g' | tr -d '\r'
```

```output
        void CCalculationTableauApproximationSaturationTaskHandleAlgorithm::applyORRule(CIndividualSaturationProcessNode*& processIndi, CConceptSaturationProcessLinker* conSatProLinker) {
          CConceptSaturationDescriptor* conDes = conSatProLinker->getConceptSaturationDescriptor();
          bool conNegation = conDes->getNegation();
          CConcept* concept = conDes->getConcept();
          if (concept->getOperandCount() == 0) {
            updateDirectAddingIndividualStatusFlags(processIndi,CIndividualSaturationProcessNodeStatusFlags::INDSATFLAGCLASHED,mCalcAlgContext);
          } else if (concept->getOperandCount() == 1) {
            STATINC(ANDRULEAPPLICATIONCOUNT,mCalcAlgContext);
            CSortedNegLinker<CConcept*>* conceptOpLinkerIt = concept->getOperandList();
            addConceptsFilteredToIndividual(conceptOpLinkerIt,conNegation,processIndi,false,mCalcAlgContext);
          } else {
            updateDirectAddingIndividualStatusFlags(processIndi,CIndividualSaturationProcessNodeStatusFlags::INDSATFLAGCRITICAL,mCalcAlgContext);
            addCriticalConceptDescriptor(conDes,CCriticalSaturationConceptTypeQueues::CCT_DISJUNCTION,processIndi,mCalcAlgContext);
            CSaturationConceptDataItem* conceptSatItem = (CSaturationConceptDataItem*)processIndi->getSaturationConceptReferenceLinking();
```

Read the three branches: an empty OR clashes; a **1-operand** OR is added deterministically (unit-strength facts flow here); a **>=2-operand** OR is only flagged `CRITICAL` and pushed onto the `CCT_DISJUNCTION` queue. No case-split. When the node *is* the disjunction's own concept node it also calls `initializeExtractDisjunctCommonConcept` — the sound rule 'if A=>X and B=>X then A|B=>X' that harvests definite subsumers *through* a disjunction with zero branching.

After the deterministic fixpoint each parked disjunction is re-checked once: it is 'sufficient' (no SAT test) iff a disjunct is already in the node's deterministic label, else the node is flagged INSUFFICIENT and only then gets a complete tableau test:

```bash
sed -n '3575,3588p' /tmp/Konclude/Source/Reasoner/Kernel/Algorithm/CCalculationTableauApproximationSaturationTaskHandleAlgorithm.cpp | sed 's/\t/  /g' | tr -d '\r'
```

```output
          bool conceptNegation = conDes->isNegated();
          CReapplyConceptSaturationLabelSet* conSet = indiProcSatNode->getReapplyConceptSaturationLabelSet(false);
          if (conSet) {
            for (CSortedNegLinker<CConcept*>* opLinkerIt = concept->getOperandList(); opLinkerIt; opLinkerIt = opLinkerIt->getNext()) {
              CConcept* opConcept = opLinkerIt->getData();
              bool opConceptNegation = opLinkerIt->isNegated()^conceptNegation;

              bool checkingNegation = opConceptNegation;
              CConcept* opCheckingConcept = getDisjunctCheckingConcept(opConcept, opConceptNegation, &checkingNegation, calcAlgContext);

              if (conSet->containsConcept(opCheckingConcept, checkingNegation)) {
                return false;
              }
            }
```

## KM's path: a full completion graph, branch every disjunction on every node

KM's hypertableau (engine/src/tableau.rs) does the opposite of both Konclude choices. (1) Existentials create **fresh anonymous successors**, so the completion graph grows to model size and the top-level disjunctions fire again on every one of those nodes. (2) A disjunction with no disjunct present is **eagerly branched** — a real DFS case-split with checkpoint/rollback per alternative.

```bash
grep -n 'let t = g.new_node(Some(s), true);' engine/src/tableau.rs
```

```output
1041:                        let t = g.new_node(Some(s), true);
1086:            let t = g.new_node(Some(s), true);
1190:                        let t = g.new_node(Some(s), true);
1709:                        let t = g.new_node(Some(s), true);
```

```bash
sed -n '1873,1879p' engine/src/tableau.rs | sed 's/\t/  /g'
```

```output
            for v in &head {
                // DOD: a refuted disjunct (Concept whose complement is present)
                // would clash on the spot. Skip it, but fold its refutation dep
                // into `accum` so the disjunction-failed conflict still records
                // exactly why this branch was dead (keeps backjumping/learning
                // sound). After unit propagation the surviving disjunction has
                // ≥2 open disjuncts, so at least two real branches remain.
```

Each iteration of that loop checkpoints the graph, asserts one disjunct (`resolve_head`), recurses into `expand_inc`, and rolls back on failure — a genuine DFS case-split. With 31 binary top-level disjunctions firing on every node of a model-sized graph, that is the combinatorial blow-up: 5303's first model build alone does 75k+ branch tries (measured under KM_TAB_STATS). Konclude opens **zero** branches on the same input.

## Where we diverge — three concrete points

| | Konclude | KM hypertableau |
|---|---|---|
| **Model nodes** | one shared node per (concept, polarity); exists reuses the filler's node => bounded by #concepts | fresh anonymous successor per exists => bounded by model size; top-disjunctions re-fire on each |
| **Disjunctions** | parked `CRITICAL`, **never split**; definite consequences harvested via `initializeExtractDisjunctCommonConcept` (A=>X and B=>X gives A|B=>X) | **eagerly case-split** with checkpoint/rollback DFS |
| **Completeness work** | a full SAT test runs **only** for nodes flagged `INSUFFICIENT` (~5%) | the complete reasoner (CB or full HT) runs over the **whole** ontology for every classification |

The deepest divergence is the middle row. Konclude derives subsumers *through* disjunctions deterministically; a real branch is the rare exception. KM's HT treats every disjunction as a branch point first and prunes after. KM already owns the deterministic primitives (`saturate_inc`, the `elc` completion core) but does not use them as a *non-branching disjunction filter* inside HT classification.

## What this session's experiments confirmed

Two flags were added to KM's HT to import the missing determinism: `KM_HT_CONTRA` (generate the contrapositive Horn clauses A and B => bottom, hence A=>notB and B=>notA, so negatives propagate) and `KM_HT_DOD` (DPLL unit-propagation: assert a disjunction's last open disjunct instead of branching). Both build clean (111 tests pass) and are sound, but **neither closes 5303** — it still times out. That matches this trace: contrapositives + unit-propagation make *individual* disjunctions cheaper, but they do **not** change the two structural facts above — KM still builds a model-sized graph and still re-derives every top-disjunction per node. The lever the trace points at is Konclude's actual architecture: a **shared-node, non-branching saturation that filters concepts and only SAT-tests the INSUFFICIENT residue** — i.e. wire `elc`/`saturate_inc` in as a per-concept residue gate ahead of HT, rather than making the branch cheaper.

## Correction discovered while tracing: KM has TWO HT engines

`run_json` (engine/src/tableau.rs:4482) routes any ALC(H) KB (no number/inverse/nominals — which 5303 and the whole disjunction family are) to **`hypertableau::Ht`** (engine/src/hypertableau.rs) whenever `KM_HT=1`, and the orchestrator always sets `KM_HT=1`. The `Tableau` in tableau.rs is only the out-of-fragment fallback. So 5303 runs on `Ht`, not `Tableau`.

`Ht` already implements decision-on-demand: `eval_disj` (hypertableau.rs:932-936) returns Clash / **Unit (propagate, no branch)** / Branch exactly as DPLL would, plus `KM_HT_NEGTRIED` (assert the complement of a clashed disjunct) and `KM_HT_WATCH` (incremental unit propagation). But it detects a 'dead' disjunct only by its complement being **present** (line 924-925), and an empty-head clash clause A and B => bottom merely `raise_clash` when both are present (apply_head, line 667) — it **never derives** ¬A or ¬B. So `Ht`'s unit-propagation machinery is starved of the negative facts that would feed it. That — not a missing DPLL loop — is the real, in-the-live-engine gap, and it is where the contrapositive enrichment (A and B => bottom, therefore A=>¬B and B=>¬A) belongs. The CONTRA/DOD code added this session went into tableau.rs (the fallback) and never executed on 5303; the corrected target is `Ht::new`.
