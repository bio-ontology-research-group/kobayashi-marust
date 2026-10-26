---
name: project_km_nominals_cb
description: "Nominal completeness: Phases 0-3 ALL IMPLEMENTED (KM_NOMINALS=1; Phase 2 Nom/Join/(*) 7a2279b, Lean cert 967526e): all 6 probes pass incl. nom_oiq (Example 3, needs Nom); K+K'' width (paper's K too narrow); pending 60-ont A/B + perf before default-on"
metadata:
  type: project
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

**2026-06-12 PHASES 0–3 IMPLEMENTED** (flag KM_NOMINALS=1, default off).
Phases 0+1: commits 8a3dedf, 5f34735, 9f70802, d4d9e8e, 3b54f23.
Phase 2 (Join + r-Succ (*) + Nom): commit 7a2279b. Phase 3 (Lean soundness):
commit 967526e (`lean/ContextCalculus/Nominals.lean`, sorry-free, typechecks).

- **All 6 probes pass via the full pipeline**, each HermiT-verified:
  nom1, nom2, nom_dl8, nom_neg1 (clean), nom_unsat (inconsistent), and NEW
  **nom_oiq (= paper Example 3, oracle/ontologies/nom_oiq_funct.ofn)** —
  A ⊑ C through functionality + inverse + nominal, the first KM derivation
  REQUIRING additional nominals. Engine-level unit tests in engine.rs
  (nom_rule_oiq_example3 + negative control + filler merge + ground clash).
- **Nom width finding**: Table 3's K disjuncts are UNSOUND when K'' > K
  (K'' = distinct pinned f(o') terms in the replaced y-equalities; witness:
  head z1≈f(x) ∨ z1≈g(x) with K=1). The paper's proof silently uses
  max(K,K''); the cleanly provable bound is the SUM (n−1)+K'' (Lean
  `nom_cover`, elementary pigeonhole induction). Engine emits K+K''.
- **Two subtle enabling fixes**: (1) ground-context Hyper must include the
  SIDE clause as a candidate at non-side body positions (S(x,z1)∧S(x,z2)
  matching the same S(o,y) hypothesis twice IS the Nom trigger; self-pairs
  are provably redundant elsewhere, so this is ground-ctx-gated);
  (2) sym_groups strict pruning must admit the equal-y assignment in the
  ground ctx. Without these, Nom never fires (first test failure).
- **r-Pred head-individual exemption**: the 3b54f23 edge-per-mentioned-
  individual filter blocked ALL Nom conclusions (y≈o' mentions a fresh
  nominal no context announced). Now: body atoms discharged per-atom over
  different edges of one source (paper's per-A_i edges), ground C_i copied
  when announced, heads exempt.
- **owl_classify stdin race fixed** (writer thread vs communicate flush —
  probes crashed the pipeline on fast exits).
- Lean cert: NModel semantics (individuals + f(o) comps), evalT_shift_const,
  join_sound (= resolution_sound instance), join3_sound, rsucc_taut_sound,
  nom_cover + nom_sound (conservative-extension soundness, interpretation of
  fresh constants constructed). Build: `lake env lean
  ContextCalculus/Nominals.lean` on the laptop (mathlib-free import chain).
- **Phase-2 livelock FIXED (1ad0af6)**: the per-source r-Pred path let
  body-empty ground clauses pass the discharge check vacuously → every
  ground fact sprayed to every context with a root edge (10594: 3.5M+ Pred
  msgs, ok→timeout). Fix = restore the announcement guard (edge per
  mentioned individual) EXEMPTING additional nominals (id ≥ nom_base — the
  only thing Nom conclusions need). Result: 10594 = 192 s, FASTER than the
  Phase-1 engine (280 s same host), identical published output (+6 internal
  Q_* pairs only). Diagnosis tool: KM_PROF msgloop now prints succ/pred
  counts + ground_wo.
- **60-ont A/B DONE (2026-06-12, fixed binary, res_nom_ab.jsonl): 59 onts,
  31 ok — ALL 31 gold-equal, 0 disagreements** → KM_NOMINALS correctness is
  corpus-validated. 28 timeouts of which 16 nominal-INDUCED (base-ok onts:
  148, 1481, 15846, 16462, 1790, 2453, 3050, 6765, 6999, 960, 7474, 8322,
  8480, 8999, 9654, 9881 — e.g. 960 base 0.9s) — BUT measured on the
  CONTENDED head node (KM_THREADS=4 nice 15, concurrent builds): re-run on
  cluster nodes for fair numbers before perf work. Default-on blocked on
  perf only; correctness + Lean soundness are done. ws still unreachable
  (since 2026-06-12 ~16:00; unimatrix ~/km-build is the build host).

See [[project_km_sweep5976]] for the SROIQ-sans-datatypes 0-unsound milestone
and [[project_km_completeness_gaps]] for the overall map (datatypes = next).
