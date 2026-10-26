---
name: project_km_cardinality_recognition
description: "16461 min-card gap FIXED (3 parts: >=n recognition clause polarity-gated, fact-only successor cores, symmetric Hyper pruning); commit fd94c7e; sweep 5941 validating; 15672 joins live-disjunction timeouts"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

The [[project_km_completeness_gaps]] 16461 qualified-min-cardinality gap is
FIXED (commit fd94c7e on payg-strategy, 2026-06-12, NOT pushed). Three parts:

1. **Frontend recognition clause** (normalise.rs AtLeast): n>=2 now emits
   `r(x,y0..y_{n-1}) ∧ F(y_i) -> Q(x) | ⋁ yi≈yj` (contrapositive
   ¬Q ⊑ ≤(n-1) r.F; the engine already handled the AtMost shape). Was
   n==1-only, so LHS min-cards NEVER fired. POLARITY-GATED via mark_polarity
   pre-pass: skip only when proven positive-only (unseen => emit).

2. **Engine fact-only successor cores** (engine.rs propagate/Succ): the
   central strategy pushed DISJUNCTIVELY-derived triggers into successor
   cores; the returning PredClause then conditioned on the whole core =
   impossible simultaneous multi-cut from one clause => per-disjunct
   refutations unavailable => n>=3 recognition stalled even with the clause
   present (n=2 worked: single cut). Rule: a trigger enters the core iff it
   is the SOLE succ-trigger over its f in the source clause head; otherwise
   it stays a hypothesis p->p (Context.fact_trigger_sets). KM_NO_CENTRAL
   (legacy, pure hypotheses) never had the gap — that confirmed diagnosis.
   First unit-only-facts version was too strict: DOLCE-style disjunctions
   all became hypotheses => 15672 churned. Sole-trigger-per-(clause,f) is
   the exact completeness criterion (single cuts always possible, residues
   accumulate normally).

3. **Symmetric-group Hyper pruning** (clause.rs sym_groups + engine.rs
   sym_groups_ok): OntologyClause precomputes exchange-invariant
   neighbour-var groups (pairwise swap-invariance + union-find); hyper_join
   enumerates only term-sorted assignments per group (strict when head has
   eq for every pair => equal-term = tautology). Side-position vars exempt
   (side clause pinned). Output-preserving (canon-identical resolvents).

**Probes** (ws:/tmp): card_probe (n=2), probe_n2_chain (2-level filler
chain), probe_n3, probe_n4_exact, probe_n4_direct, all PASS; full 16461
derives Patient1 ⊑ Systemic_JIA_Patient (the 1 missing-vs-gold sub; needs
≥4 hasAffectedJoint.Joint over 5 pairwise-disjoint joints). Tests:
min_cardinality_recognition{,_three_witnesses}, atleast_two_recognition_clause,
atleast_recognition_polarity_gated (53+16 pass).

**Validation**: output identical vs deployed arena binary on 9944 (315,940
exact — NOTE ws:/tmp/km-baseline is STALE, predates the d3a0e1e ordering
fix, gives 300,526; compare against /tmp/km-deployed instead), 12698-core,
dhv, 13912, 6720, 14896. ofn byte-identical on 10 card-free onts. kmcard
job 5935 (70 affected onts, pre-gating): only corpus regression was 15672.

**15672 (DOLCE)**: its genuinely-negative unqualified ≥5 setting-for
recognition (EquivalentClasses conjunct) doubles pipeline wall — ONE added
clause; residues of recognition resolvents create new Hyper providers,
mutually incomparable => live-disjunction feedback. ok->timeout accepted;
member of the ordered-resolution workstream family now. Single-threaded
15672 ALWAYS timed out (sweep ok came from parallel pipeline; both old/new
peak ~18.9GB vs KM_PAR_MEM_GB=18 watchdog — it sits exactly at the edge).

**Deployed** to unimatrix ~/bench/km/ (ofn md5 ab563d2b, engine cd152a47;
.bak-precard backups). Full sweep = job 5941 (results res_kmbatch_*.jsonl,
overwrites 5905's). Expected: 16461 incomplete->agree, 15672 ok->timeout,
everything else unchanged. AtMost-on-LHS recognition (≤n ⊑ G) is a separate
still-open gap (no recognition clausification at all) — never exercised on
ORE so far.
