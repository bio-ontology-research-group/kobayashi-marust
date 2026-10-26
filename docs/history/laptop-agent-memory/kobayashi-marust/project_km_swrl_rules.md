---
name: project_km_swrl_rules
description: "SWRL DL-safe rule support (2669/15516) — design, feasibility findings, Stage 1 done"
metadata: 
  node_type: memory
  type: project
  originSessionId: 666845f8-0818-4d3e-8e4f-a3e9496633db
---

2026-06-27: Closing ore_ont_2669 + 15516 (DL-safe SWRL DLSafeRule onts; HermiT=INCONSISTENT, Konclude CANNOT parse them — the 2 SWRL onts in the user's all-onts goal).

**Structure (2669)**: 8 DLSafeRules (15516: 2). Rules are GRAPH-shaped, up to 8 vars, joins over isPartOf/references/hasPart (NOT tree-shaped — e.g. `br` has two predecessors op1,op2). 270 ClassAssertion + 413 ObjectPropertyAssertion (~180 named individuals, all pairwise DifferentIndividuals). Inconsistency = rules derive hasInversePropertyMapping/hasDomainMapping/hasRangeMapping facts that violate FunctionalObjectProperty/InverseFunctional + 8 DisjointClasses.

**Why hard (evidence)**: rule bodies need DERIVED facts, not asserted. isPartOf has 0 asserted edges (it's inverse of hasPart, 280 asserted hasPart). Body classes BinaryObjectPropertyMapping/UnaryObjectPropertyMapping = 0 ClassAssertions; defined by COMPLEX ALC EquivalentClasses (negation + nested ∃ over isPartOf/hasPart/references). ⇒ firing rules needs FULL ABox realization over complex definitions, not a lightweight closure.

**KM capabilities (2 Explore agents)**: NO individual materialization (engine outputs class-class subsumptions only; no instances()/realize()). BUT KM ALREADY detects ABox inconsistency (disjoint-class clash AND functional-role clash both → `"consistent": false`, tested on ws). HT `rec_match_flex` (hypertableau.rs:1305) = GENERAL multi-var graph-body matcher over the node graph (Subst of nvars, binds through edges either direction) — handles graph rules natively. `apply_head` (1406): empty head→raise_clash. Nominal o-rule (process_nominals→merge_into) builds nominal nodes. cb_to_ht::convert only matches JTerm::Var, DROPS ground JTerm::Ind facts. CB engine term scheme (X/Y/zvar) = depth-1 star only ⇒ graph rules NOT expressible as single CB clause.

**DESIGN (HT-native, no Lean re-cert — rules are standard DL-clauses)**: gate KM_HT_RULES (default OFF). (1) plumb parsed rules frontend→cb_to_ht. (2) seed ABox as named-individual nominal nodes ({a}⊑C, {a}⊑∃r.{b}); STOP dropping Ind facts. (3) rules→HtClauses, vars as Subst idx, O-GUARD __O__(v) per var (DL-safety; firing on anon nodes=UNSOUND) + x≠y filter for DiffInd (op1=op2 firing=spurious functional clash=UNSOUND). (4) route rules-onts to HT global consistency. SOUNDNESS-CRITICAL: O-guard+x≠y exact or consistent onts flip inconsistent.

**Stage 1 DONE+committed (706f573)**: frontend Axiom::Rule + RuleAtom/RuleTerm + DLSafeRule parse; unrepresentable atom⇒drop rule (sound). 172 tests; real 2669→8 / 15516→2 rules (exact). Ontology::rules(); KM_DEBUG_RULES prints count. Inert until HT consumes.

**Stage 2 DONE+committed (ea0d535)**: gated KM_HT_RULES. Routes rule-onts to a rule-aware HT consistency check: ground ABox (CB drops it) seeded as named nominal nodes ({a}⊑C, {a}⊑∃r.{b}); rules→O-guarded HtClauses fired over named individuals (rec_match_flex); rules with Same/Diff/complex-class atoms DROPPED (sound). The 2669/15516 closure is actually from the ABox-SEEDING (their rules all have DiffInd→dropped); inconsistency is rule-INDEPENDENT (salary:DBNonKeyAttribute⊑DBNonPrimaryKeyAttribute⊑DBKeyAttribute vs Disjoint(DBKeyAttribute,DBNonKeyAttribute)), which CB missed by dropping the ABox.

**Stage 3 DONE+committed (0d20dd1, 2026-07-05): DEFAULT-ON, rule-gated. +3
recoveries (2669/15516/10906).** Flipped KM_HT_RULES→default (opt out
KM_NO_HT_RULES). Made SAFE corpus-wide by gating everything on ACTUAL rule
presence: (1) frontend collect_rules default-on but EMPTY on rule-free ont →
ht_rules false → byte-identical clause output; (2) cb_to_ht `rules_active =
ht_rules && !rules.is_empty()` gates ABox-nominal seed + ground-fact intercept
+ the emelim SUPPRESSION (emelim being globally disabled was THE blocker to
default-on; now only suppressed on rule onts); (3) mod.rs rules-consistency now
short-circuits ONLY on inconsistency — a CONSISTENT rule ont FALLS THROUGH to
normal classify so its hierarchy is computed (DL-safe rules = named-indiv only
⇒ cannot change TBox subsumption ⇒ fall-through sound+complete; previously it
returned empty subs unconditionally = would drop every consistent rule ont's
hierarchy). Validated all 6: 2669/15516/10906 timeout→inconsistent (0.16-0.17s),
13129 consistent 83==83 subs IDENTICAL, 12451/10860 unchanged timeout. +3/0-reg,
1390 tests. Closes 2669+15516 from the tracked-10 list. Corpus-panel-on-IBEX
still pending for the full-587 confirmation.

**SOUNDNESS VERIFIED (HermiT authority — Konclude AND HermiT both CANNOT parse raw DLSafeRule onts: datatype rdfs:Literal / builtin-atom exceptions, so ALL 6 have BOGUS Konclude "consistent" gold).** 6 ORE rule-onts = 2669 15516 10860 10906 12451 13129. KM_HT_RULES=1 verdicts ALL CORRECT vs HermiT-on-cleaned-core (strip Data*/DLSafeRule; cleaned⊆full so cleaned-inconsistent⟹full-inconsistent): 2669/15516/10906→INCONSISTENT (HermiT-confirmed), 13129→consistent (HermiT-confirmed satisfiable), 12451→consistent(HermiT)/KM-timeout, 10860→KM-timeout. ZERO unsound; KM closes 2669/15516/10906 correctly + 13129 correct-consistent. Gated OFF=byte-identical(172 tests), controls rule_ok→consistent/rule_clash→inconsistent. So 10906 is a NEW contested-gold inconsistent ont (like 2669/15516). Onts: ws:/tmp/o{2669,15516,10860,10906,12451,13129}.owl; cleaned cores unimatrix:/tmp/clean_{10906,13129}.owl.
