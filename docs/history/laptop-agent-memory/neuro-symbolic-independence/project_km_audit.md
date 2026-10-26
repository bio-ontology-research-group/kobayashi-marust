---
name: project_km_audit
description: "Multi-agent faithfulness audit of the KM Rust engine (2026-06-04) — 7 confirmed bugs, all fixed + re-certified"
metadata: 
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Fanned-out multi-agent code audit of the kobayashi-marust Rust engine vs the
verified calculus (workflow: 7 module auditors → adversarial verify each finding →
synthesis; 31 agents, ~1.5M tokens). Auditors instrumented the live engine to
confirm. **7 confirmed findings, ALL FIXED + oracle-validated + Lean-recertified**
on branch `payg-strategy` (PR #2):

- **H1 SOUNDNESS (commit dd821c8):** `Pred` push-back gate (engine.rs:1069) admitted
  function-free Eq/Ineq head disjuncts; apply_pred then DROPPED them (kept only
  Lit::P) → strengthened clause → spurious empty clause / false owl:Nothing /
  false inconsistency. Witness `Q⊑∃R.⊤ + R(z1,x)→x≈z1` wrongly made Q unsat. Fix:
  require head literals be `Lit::P` in the gate (exclude Eq/Ineq). THE only
  soundness breach. (The per-run cert checker doesn't run in the normal classify
  path, so this reached the API.)
- **H2/M1 COMPLETENESS (commit 8964caf):** `pred_lteq` (calc.rs) was not term-major:
  (H2) internal-disjunct shortcut ignored terms → C_internal(f(x)) & D_named(x)
  mutually `<=` → max_head emptied → clause inert (Succ silenced) in non-root
  contexts; (M1) role ranked by SOURCE term not max(s,t) → term-maximal succ role
  dropped. Fix: gate internal-disjunct to same-term + compare TERM-MAJOR (max_term
  first) with deterministic tie-break. Also fixes the non-transitivity (clarity).
- **M2 COMPLETENESS/consistency-API (commit 42848f0):** `inconsistent()` only fired
  if a concept LITERALLY named owl:Thing derived ⊥, but the normaliser maps
  owl:Thing to an internal proxy → dead check → inconsistent ontologies reported
  consistent. Fix: `run_for` seeds a ⊤ (empty-core, query=None) context; inconsistent()
  checks IF ⊤ derives ⊥. (Cheap "any/all named unsat" alternatives are each unsound
  one way.) Verified: {→Q(x),Q(x)→,A⊑B} now inconsistent=true.
- **L1/L2 (commit af61052):** 5,000,000-message fixpoint cap broke SILENTLY → now
  emits stderr WARNING (incomplete/truncated run).

**Validation after every fix:** cargo test 6/6; HermiT oracle 6/6 with 0 unsound /
0 missing (kinship 21/21, factor [A,Bad], trans 2/2, chain 1/1) — verdicts
unchanged on the 6 onts, so no regression. **Lean re-certification REDONE per the
standing rule** ("change logic → redo Lean cert"): regenerated all
lean/Validation/*.lean certs from the fixed engine (7 JSON certs byte-identical;
Kinship/Transtest only cosmetic renumbering drift, restored to HEAD), `lake build
Validation` GREEN on ws (every verdict kernel-checked).

**STILL TO DO:** (1) sync fixed engine.rs+calc.rs to the vendored paper crate
`sroiq-nesy/rust-context-reasoner/`. (2) BENCHMARK CAVEAT: the running ORE benchmark
(unimatrix01) uses the OLD binary `~/bench/km/kobayashi-marust-par` (pre-fix) — its
KM results reflect the BUGGY engine (H1 → KM may show false owl:Nothing/unsound vs
gold on some onts; H2/M1 → KM more incomplete than necessary). For an honest paper
benchmark on the FIXED engine, rebuild+redeploy `kobayashi-marust-par` and re-run.
Synthesis full report: workflow w9mawfz81 transcript.
See [[project_km_reasoner_perf]] [[project_km_reasoner_benchmark]] [[project_disjunctive_context_calculus]].
