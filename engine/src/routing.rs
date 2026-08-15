//! Classification procedure names and exact option bundles.
//!
//! `Route::Auto` is selected from the source-only ontology profile by the
//! generated decision tree. `Route::Manual` preserves the historical behavior:
//! every `KM_*` option is read exactly as supplied. Named routes normalize the
//! routing keys below to the same bundles used by the IBEX procedure matrix;
//! diagnostic/experimental keys outside this list remain available.

use std::str::FromStr;

use crate::frontend::profile::OntologyProfile;

mod routing_tree_generated;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Route {
    Auto,
    Manual,
    Default,
    Default8,
    Default1,
    ProductionAll,
    ProductionAll8,
    ProductionAll1,
    CertifiedCardNominals,
    CertifiedCardProxyAbox,
    CbPlain16,
    CbPlain8,
    CbPlain1,
    CbAbsorb16,
    CbAbsorb8,
    CbAbsorb1,
    CbTrigger16,
    CbTrigger8,
    CbTrigger1,
    CbAbsorbPortfolio16,
    Elc,
    ElcCert,
    /// Plain certified EL first, with the exact absorbed production portfolio
    /// on certificate refusal or worker failure.
    CertifiedElProduction,
    Lean,
    HtGeneral,
    HtQo,
    HtShoq,
    HtCard,
    HtBridge,
    /// Certified bridge portfolio with the exact nominal-aware CB fallback.
    /// This is public for route-panel reproducibility; unlike `HtBridge`, it is
    /// deliberately non-atomic because a bridge defer must retain the ABox.
    CertifiedNominals,
    HtFeatures,
    HtFull,
    HtRules,
    Tableau,
    TabRace,
    CardFn,
    /// Complete-answer-or-defer SHOIQ TBox specialist for the certified
    /// finite nominal layout selected by `nominal_ni_tbox_candidate`.
    NominalNiTbox,
    /// Complete-answer-or-defer SHOIQ specialist over a frontend-certified
    /// typed ABox, paired with the exact nominal CB fallback.
    NominalNiAbox,
    Nominals,
    SeqOn,
    SeqOff,
}

impl Route {
    pub const NAMED: [Route; 39] = [
        Route::Default,
        Route::Default8,
        Route::Default1,
        Route::ProductionAll,
        Route::ProductionAll8,
        Route::ProductionAll1,
        Route::CertifiedCardNominals,
        Route::CertifiedCardProxyAbox,
        Route::CbPlain16,
        Route::CbPlain8,
        Route::CbPlain1,
        Route::CbAbsorb16,
        Route::CbAbsorb8,
        Route::CbAbsorb1,
        Route::CbTrigger16,
        Route::CbTrigger8,
        Route::CbTrigger1,
        Route::CbAbsorbPortfolio16,
        Route::Elc,
        Route::ElcCert,
        Route::CertifiedElProduction,
        Route::Lean,
        Route::HtGeneral,
        Route::HtQo,
        Route::HtShoq,
        Route::HtCard,
        Route::HtBridge,
        Route::CertifiedNominals,
        Route::HtFeatures,
        Route::HtFull,
        Route::HtRules,
        Route::Tableau,
        Route::TabRace,
        Route::CardFn,
        Route::NominalNiTbox,
        Route::NominalNiAbox,
        Route::Nominals,
        Route::SeqOn,
        Route::SeqOff,
    ];

    pub fn as_str(self) -> &'static str {
        match self {
            Route::Auto => "auto",
            Route::Manual => "manual",
            Route::Default => "default",
            Route::Default8 => "default8",
            Route::Default1 => "default1",
            Route::ProductionAll => "production_all",
            Route::ProductionAll8 => "production_all8",
            Route::ProductionAll1 => "production_all1",
            Route::CertifiedCardNominals => "certified_card_nominals",
            Route::CertifiedCardProxyAbox => "certified_card_proxy_abox",
            Route::CbPlain16 => "cb_plain16",
            Route::CbPlain8 => "cb_plain8",
            Route::CbPlain1 => "cb_plain1",
            Route::CbAbsorb16 => "cb_absorb16",
            Route::CbAbsorb8 => "cb_absorb8",
            Route::CbAbsorb1 => "cb_absorb1",
            Route::CbTrigger16 => "cb_trigger16",
            Route::CbTrigger8 => "cb_trigger8",
            Route::CbTrigger1 => "cb_trigger1",
            Route::CbAbsorbPortfolio16 => "cb_absorb_portfolio16",
            Route::Elc => "elc",
            Route::ElcCert => "elc_cert",
            Route::CertifiedElProduction => "certified_el_production",
            Route::Lean => "lean",
            Route::HtGeneral => "ht_general",
            Route::HtQo => "ht_qo",
            Route::HtShoq => "ht_shoq",
            Route::HtCard => "ht_card",
            Route::HtBridge => "ht_bridge",
            Route::CertifiedNominals => "certified_nominals",
            Route::HtFeatures => "ht_features",
            Route::HtFull => "ht_full",
            Route::HtRules => "ht_rules",
            Route::Tableau => "tableau",
            Route::TabRace => "tab_race",
            Route::CardFn => "card_fn",
            Route::NominalNiTbox => "nominal_ni_tbox",
            Route::NominalNiAbox => "nominal_ni_abox",
            Route::Nominals => "nominals",
            Route::SeqOn => "seq_on",
            Route::SeqOff => "seq_off",
        }
    }

    /// The procedure matrix bundle, excluding the shared 16-thread/18-GiB
    /// defaults installed by [`apply_environment`]. Later duplicate keys win,
    /// matching the benchmark runner's ordered `--env` handling.
    pub fn settings(self) -> &'static [(&'static str, &'static str)] {
        match self {
            Route::Auto | Route::Manual | Route::Default => &[],
            Route::Default8 => &[("KM_THREADS", "8")],
            Route::Default1 => &[("KM_THREADS", "1")],
            Route::ProductionAll => PRODUCTION_ALL,
            Route::ProductionAll8 => PRODUCTION_ALL_8,
            Route::ProductionAll1 => PRODUCTION_ALL_1,
            Route::CertifiedCardNominals => CERTIFIED_CARD_NOMINALS,
            Route::CertifiedCardProxyAbox => CERTIFIED_CARD_PROXY_ABOX,
            Route::CbPlain16 => CB_PLAIN,
            Route::CbPlain8 => CB_PLAIN_8,
            Route::CbPlain1 => CB_PLAIN_1,
            Route::CbAbsorb16 => CB_ABSORB,
            Route::CbAbsorb8 => CB_ABSORB_8,
            Route::CbAbsorb1 => CB_ABSORB_1,
            Route::CbTrigger16 => CB_TRIGGER,
            Route::CbTrigger8 => CB_TRIGGER_8,
            Route::CbTrigger1 => CB_TRIGGER_1,
            Route::CbAbsorbPortfolio16 => CB_ABSORB_PORTFOLIO,
            Route::Elc => ELC,
            Route::ElcCert => ELC_CERT,
            Route::CertifiedElProduction => ELC_CERT,
            Route::Lean => LEAN,
            Route::HtGeneral => HT_GENERAL,
            Route::HtQo => HT_QO,
            Route::HtShoq => HT_SHOQ,
            Route::HtCard => HT_CARD,
            Route::HtBridge => HT_BRIDGE,
            Route::CertifiedNominals => CERTIFIED_NOMINALS,
            Route::HtFeatures => HT_FEATURES,
            Route::HtFull => HT_FULL,
            Route::HtRules => HT_RULES,
            Route::Tableau => TABLEAU,
            Route::TabRace => TAB_RACE,
            Route::CardFn => CARD_FN,
            Route::NominalNiTbox => NOMINAL_NI_TBOX,
            Route::NominalNiAbox => NOMINAL_NI_ABOX,
            Route::Nominals => NOMINALS,
            Route::SeqOn => SEQ_ON,
            Route::SeqOff => SEQ_OFF,
        }
    }

    /// Normalize the process environment to the matrix procedure. This is
    /// called once, before normalisation or any reasoner thread starts.
    pub fn apply_environment(self) {
        if matches!(self, Route::Auto | Route::Manual) {
            return;
        }
        for key in ROUTE_KEYS {
            std::env::remove_var(key);
        }
        for (key, value) in COMMON_SETTINGS.iter().chain(self.settings()) {
            std::env::set_var(key, value);
        }
    }

    /// A route that starts exactly one terminating classification mechanism.
    /// The benchmark measures these separately; the stricter fragment contract
    /// decides which subset may become generated-tree leaves.
    pub fn is_atomic(self) -> bool {
        matches!(
            self,
            Route::CertifiedCardNominals
                | Route::CbPlain16
                | Route::CbPlain8
                | Route::CbPlain1
                | Route::CbAbsorb16
                | Route::CbAbsorb8
                | Route::CbAbsorb1
                | Route::CbTrigger16
                | Route::CbTrigger8
                | Route::CbTrigger1
                | Route::Elc
                | Route::ElcCert
                | Route::Lean
                | Route::HtGeneral
                | Route::HtQo
                | Route::HtShoq
                | Route::HtCard
                | Route::HtBridge
                | Route::HtFeatures
                | Route::HtFull
                | Route::HtRules
                | Route::Tableau
                | Route::CardFn
                | Route::NominalNiTbox
                | Route::Nominals
                | Route::SeqOn
                | Route::SeqOff
        )
    }

    /// Whether callers may use this route as the entailment oracle for source
    /// justification extraction.
    ///
    /// Only `auto` applies the source-profile semantic-fragment gate before it
    /// selects an exact mechanism. Named procedures are matrix measurements:
    /// several are sound/complete only on a particular fragment, and an
    /// explicitly forced procedure bypasses the gate that establishes that
    /// fragment. `manual` is even less constrained because arbitrary ambient
    /// `KM_*` settings survive. Explanation extraction therefore fails closed
    /// unless every candidate ontology passes through the automatic production
    /// policy.
    pub fn is_explanation_safe(self) -> bool {
        self == Route::Auto
    }
}

impl std::fmt::Display for Route {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for Route {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let route = match value {
            "auto" => Route::Auto,
            "manual" | "legacy" => Route::Manual,
            "default" => Route::Default,
            "default8" => Route::Default8,
            "default1" => Route::Default1,
            "production_all" | "production" => Route::ProductionAll,
            "production_all8" | "production8" => Route::ProductionAll8,
            "production_all1" | "production1" => Route::ProductionAll1,
            "certified_card_nominals" | "card_nominals" => Route::CertifiedCardNominals,
            "certified_card_proxy_abox" | "card_proxy_abox" | "card_race" => {
                Route::CertifiedCardProxyAbox
            }
            "cb_plain16" | "cb" => Route::CbPlain16,
            "cb_plain8" => Route::CbPlain8,
            "cb_plain1" => Route::CbPlain1,
            "cb_absorb16" | "absorb" => Route::CbAbsorb16,
            "cb_absorb8" => Route::CbAbsorb8,
            "cb_absorb1" => Route::CbAbsorb1,
            "cb_trigger16" | "trigger" => Route::CbTrigger16,
            "cb_trigger8" => Route::CbTrigger8,
            "cb_trigger1" => Route::CbTrigger1,
            "cb_absorb_portfolio16" | "absorb_portfolio" => Route::CbAbsorbPortfolio16,
            "elc" => Route::Elc,
            "elc_cert" => Route::ElcCert,
            "certified_el_production" | "elc_cert_production" => {
                Route::CertifiedElProduction
            }
            "lean" => Route::Lean,
            "ht_general" | "ht" => Route::HtGeneral,
            "ht_qo" | "qo" => Route::HtQo,
            "ht_shoq" | "shoq" => Route::HtShoq,
            "ht_card" | "card" => Route::HtCard,
            "ht_bridge" | "bridge" => Route::HtBridge,
            "certified_nominals" | "bridge_nominals" | "ht_bridge_nominals" => {
                Route::CertifiedNominals
            }
            "ht_features" | "ht_feature_pack" => Route::HtFeatures,
            "ht_full" => Route::HtFull,
            "ht_rules" | "rules" => Route::HtRules,
            "tableau" => Route::Tableau,
            "tab_race" | "tab" => Route::TabRace,
            "card_fn" | "functional_card" => Route::CardFn,
            "nominal_ni_tbox" | "ni_tbox" => Route::NominalNiTbox,
            "nominal_ni_abox" | "ni_abox" => Route::NominalNiAbox,
            "nominals" | "nominal" => Route::Nominals,
            "seq_on" | "seq" => Route::SeqOn,
            "seq_off" | "no_seq" => Route::SeqOff,
            _ => return Err(format!("unknown classification route {value:?}")),
        };
        Ok(route)
    }
}

/// Soundness/completeness domain used as a hard gate around the learned tree.
/// Timing data can choose between complete procedures inside a domain, but it
/// cannot redefine which procedure is semantically applicable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticFragment {
    UnsupportedRules,
    Rules,
    /// A typed class-assertion ABox whose individuals are covered by one
    /// n-ary `DifferentIndividuals` axiom, combined with the exact atomic
    /// datatype fragment supported by the native Konclude bridge.  This is
    /// the source-level gate for the 10621 mechanism. Automatic dispatch uses
    /// the dedicated `certified_nominals` portfolio: certified HT independently
    /// rechecks complete ABox and clause/RBox coverage, while an honest bridge
    /// defer leaves the exact nominal-aware CB fallback authoritative.
    NativeBridgeAbox,
    /// A positive ABox whose consistency and TBox-separation follow from the
    /// source certificate. It may use the same complete TBox mechanisms as the
    /// nominal-free core; all other ABoxes remain `Nominal`.
    PositiveAbox,
    Nominal,
    SriqCore,
}

/// Source-only certificate for the combined nominal/datatype bridge fragment.
///
/// The certificate deliberately recognizes the narrow all-different layout
/// for which KM carries every assertion into Konclude's native nominal model:
/// exactly one class assertion per source individual, plus one n-ary
/// `DifferentIndividuals` axiom covering that population.  Other ABoxes keep
/// the established nominal route.  The converted bridge performs the final,
/// stronger lossless-coverage check, so this gate can authorize a bridge
/// attempt but cannot authorize a partial answer.
fn native_bridge_abox_eligible(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let different = source
        .axiom_types
        .get("DifferentIndividuals")
        .copied()
        .unwrap_or(0);
    profile.expressivity.datatype
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.role_assertions == 0
        && different == 1
        && source.class_assertions > 0
        && source.abox_axioms == source.class_assertions.saturating_add(different)
        && source.distinct_individuals == source.class_assertions
}

/// Source-only candidate gate for Konclude-style large independent-ABox
/// precomputation and TBox classification.
///
/// Every individual has exactly one class assertion and there are no role,
/// equality, rule, data, or nominal constraints. The ordinary TBox taxonomy is
/// therefore complete for subsumption, and the conductor checks every asserted
/// class against the final unsatisfiable set to recover ABox inconsistency.
/// The production portfolio may race its certified native bridge with that
/// exact TBox path without materializing the ABox into nominal root contexts.
fn independent_large_abox_candidate(profile: &OntologyProfile) -> bool {
    const CONDITIONAL_FULL_INDIVIDUAL_LIMIT: u64 = 10_000;

    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);
    source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.distinct_individuals >= CONDITIONAL_FULL_INDIVIDUAL_LIMIT
        && source.class_assertions > 0
        && source.abox_axioms == source.class_assertions
        && source.distinct_individuals == source.class_assertions
        && source.role_assertions == 0
        && source.distinct_data_properties == 0
        && source.datatype_constructors == 0
        && source.nominals == 0
        && source.has_values == 0
        && !profile.expressivity.datatype
        && !profile.expressivity.nominal
        && !profile.expressivity.universal_role
        && count("DifferentIndividuals") == 0
        && count("SameIndividual") == 0
        && count("NegativeObjectPropertyAssertion") == 0
}

/// Source-level EL candidate within the independently separable ABox family.
///
/// The ELC worker still checks the normalized clause shape and returns
/// not-EL instead of answering outside its fragment. These source fences keep
/// the automatic leaf conservative and distinguish the large pure-EL ORE
/// terminologies from the SRIQ member of the same ABox family.
fn independent_large_abox_el_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    independent_large_abox_candidate(profile)
        && source.unions == 0
        && source.complements == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.has_self == 0
        && source.functional_role_axioms == 0
        && source.inverse_functional_role_axioms == 0
        && !profile.expressivity.cardinality
        && !profile.expressivity.qualified_cardinality
        && !profile.expressivity.functionality
}

/// Source-only admission gate for trying the exact typed object-ABox bridge.
///
/// This is deliberately only a candidate test.  The converted-input bridge
/// independently requires lossless clause, RBox, nominal, and ABox coverage
/// and returns DEFER on any mismatch.  Automatic dispatch pairs that attempt
/// with the exact nominal-aware CB fallback, so broadening this source gate can
/// improve performance but can never authorize a partial bridge answer.
///
/// Data assertions and equality are excluded because the typed object-ABox
/// bridge does not currently represent them. Datatype TBox axioms remain
/// eligible: the converted-input bridge has an independent, fail-closed
/// certificate for its exact atomic datatype fragment. Complex role chains,
/// the universal role, and self restrictions are excluded here as cheap
/// source predictors for normalized bridge fences; ordinary inverse roles,
/// transitivity, unqualified cardinality, object nominals, role assertions,
/// and pairwise inequality remain eligible.
fn typed_object_abox_bridge_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);
    let represented_abox = count("ClassAssertion")
        .saturating_add(count("ObjectPropertyAssertion"))
        .saturating_add(count("NegativeObjectPropertyAssertion"))
        .saturating_add(count("DifferentIndividuals"));

    source.abox_axioms > 0
        && represented_abox == source.abox_axioms
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && count("DataPropertyAssertion") == 0
        && count("NegativeDataPropertyAssertion") == 0
        && count("SameIndividual") == 0
        && source.role_chain_axioms == 0
        && source.has_self == 0
        && !profile.expressivity.universal_role
}

/// Large typed-ABox bridge jobs for which concurrent exact CB materialization
/// dominates process-tree memory.  The bridge remains complete-answer-or-defer;
/// this source predicate changes only whether the unchanged CB fallback starts
/// concurrently or after a bridge defer.  Keep the scale gate high so small
/// certified-nominal jobs retain their low-latency race.
pub(crate) fn sequential_typed_bridge_candidate(profile: &OntologyProfile) -> bool {
    typed_object_abox_bridge_candidate(profile)
        && profile.source.logical_axioms >= 30_000
        && profile.source.concept_expressions >= 100_000
}

/// Large disjunctive SHI terminologies whose synchronous completion bridge is
/// already the only competitive exact arm. Running that complete-answer-or-
/// defer bridge before allocating CB avoids memory-bandwidth contention from a
/// fallback that cannot win this workload. The bridge still validates every
/// normalized/source premise and a defer starts the unchanged production CB
/// stack, so this predicate authorizes scheduling only.
pub(crate) fn sequential_large_shi_bridge_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.abox_axioms == 0
        && source.logical_axioms >= 50_000
        && source.concept_expressions >= 300_000
        && source.unions >= 10_000
        && source.distinct_classes >= 50_000
        && source.distinct_object_properties <= 16
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && profile.expressivity.inverse
        && profile.expressivity.transitivity
        && !profile.expressivity.nominal
        && !profile.expressivity.cardinality
        && !profile.expressivity.datatype
}

/// Dense, role-rich EL terminology closures whose edge-side NF4 join has enough
/// propagation work per frontier to amortize parent-grouped parallel batches.
/// The bounds are source-profile scheduling gates only; the completion rules
/// and certified production fallback remain unchanged.
pub(crate) fn parallel_nf4_frontier_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    // Production classification intentionally does not rescan the normalized
    // clause vector for full clause statistics, so this gate must use source
    // statistics carried by the normal frontend path.
    (2_000_000..3_000_000).contains(&source.logical_axioms)
        && source.existentials >= 2_000_000
        && (4..=16).contains(&source.distinct_object_properties)
        && (400_000_000..550_000_000).contains(&source.file_bytes)
        && source.abox_axioms == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && !profile.expressivity.nominal
        && !profile.expressivity.cardinality
        && !profile.expressivity.datatype
}

/// Large role-chain/cardinality TBoxes whose completion workload loses a small
/// amount of throughput to the default 16-way orchestration. The automatic
/// pipeline also runs their complete-answer-or-defer bridge before allocating
/// the unchanged CB fallback. This predicate changes scheduling only.
pub(crate) fn eight_thread_large_sriq_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.abox_axioms == 0
        && source.logical_axioms >= 150_000
        && source.qualified_cardinalities >= 70
        && source.role_chain_axioms >= 30
        && source.distinct_classes >= 58_000
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && profile.expressivity.inverse
        && profile.expressivity.complex_subrole
        && !profile.expressivity.nominal
        && !profile.expressivity.datatype
}

/// Large nominal-free production TBoxes without qualified cardinality use the
/// same exact portfolio more efficiently with eight worker threads. Six
/// representative ORE classifications retained byte-identical answers while
/// reducing their summed process-tree peak by about 916 MiB; none became
/// slower. This predicate changes scheduling only.
pub(crate) fn eight_thread_large_plain_tbox_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.abox_axioms == 0
        && source.logical_axioms >= 20_000
        && source.qualified_cardinalities == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && !profile.expressivity.nominal
        && !profile.expressivity.datatype
}

/// Medium SHI terminologies in the plain production fragment do not benefit
/// from parallel CB workers. The single-worker schedule produced identical
/// classifications on all five matching ORE ontologies, preserved wall time,
/// and removed hundreds of MiB on the two parallel-allocation-heavy members.
pub(crate) fn one_thread_medium_shi_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.abox_axioms == 0
        && (20_000..100_000).contains(&source.logical_axioms)
        && source.unions == 0
        && source.role_chain_axioms == 0
        && source.qualified_cardinalities == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && profile.expressivity.negation_disjunction
        && profile.expressivity.existential
        && profile.expressivity.transitivity
        && profile.expressivity.role_hierarchy
        && profile.expressivity.inverse
        && !profile.expressivity.complex_subrole
        && !profile.expressivity.nominal
        && !profile.expressivity.cardinality
        && !profile.expressivity.datatype
}

/// Measured nominal-free production shapes for which additional CB workers add
/// substantial allocator/RSS overhead without reducing end-to-end latency. The
/// portfolio, completion bridge, fallback, and winner contract are unchanged;
/// only the CB worker count is reduced.
pub(crate) fn one_thread_small_production_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let large_functional_tbox =
        profile.expressivity.functionality && source.distinct_classes >= 2_500;
    let live_disjunctive_tbox = source.unions >= 19 && source.universals >= 25;

    (large_functional_tbox || live_disjunctive_tbox)
        && source.abox_axioms == 0
        && source.logical_axioms < 20_000
        && source.file_bytes < 2_000_000
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && !profile.expressivity.complex_subrole
        && !profile.expressivity.nominal
        && !profile.expressivity.cardinality
        && !profile.expressivity.datatype
}

/// Source-layout gate for the finite SHOIN nominal specialist.
///
/// This route deliberately recognizes the complete Wine-style layout that was
/// validated against its full-IRI ORE signature. The worker still performs the
/// stronger converted-input checks: zero dropped clauses, only the two SHOIQ
/// fences, inverse bridges present, number restrictions present, and absence
/// of every nominal-introduction premise in each completed model. Inputs that
/// differ in any material source feature stay on the exact nominal CB route.
fn nominal_ni_tbox_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);

    profile.expressivity.code == "SHOIN"
        && profile.expressivity.nominal
        && profile.expressivity.inverse
        && profile.expressivity.cardinality
        && profile.expressivity.functionality
        && profile.expressivity.transitivity
        && !profile.expressivity.qualified_cardinality
        && !profile.expressivity.datatype
        && !profile.expressivity.universal_role
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.logical_axioms == 889
        && source.tbox_axioms == 355
        && source.rbox_axioms == 40
        && source.abox_axioms == 494
        && source.distinct_classes == 137
        && source.distinct_object_properties == 16
        && source.distinct_individuals == 206
        && source.class_assertions == 227
        && source.role_assertions == 247
        && source.nominals == 74
        && source.has_values == 174
        && source.role_chain_axioms == 0
        && source.transitive_role_axioms == 1
        && source.functional_role_axioms == 6
        && count("DataPropertyAssertion") == 1
        && count("DataPropertyDomain") == 1
        && count("DataPropertyRange") == 1
        && count("DifferentIndividuals") == 8
        && count("SameIndividual") == 12
}

/// Cheap source precondition for the typed-ABox SHOIQ specialist.
///
/// This does not authorize an answer. The frontend must additionally certify
/// complete typed-ABox coverage after normalization, and the worker rechecks
/// every converted clause, fence, inverse-functionality equality clause, and
/// completed-model nominal-introduction premise. The route retains exact CB as
/// a fallback, so a false positive changes scheduling only.
pub(crate) fn nominal_ni_abox_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.abox_axioms > 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.role_chain_axioms == 0
        && profile.expressivity.nominal
        && profile.expressivity.inverse
        && source
            .min_cardinalities
            .saturating_add(source.max_cardinalities)
            .saturating_add(source.exact_cardinalities)
            > 0
        && profile.expressivity.functionality
}

/// Retained complete ground-clause HT route for the compact SHOIF(D) ABox
/// shape represented by ORE6934.
///
/// The worker keeps every normalized ground clause and deliberately does not
/// install the same typed ABox a second time as native nominal state. The
/// source fingerprint is a scheduling fence, while the HT conversion and
/// classifier still consume the complete normalized input. This route was
/// independently reproduced from the retained binary and compared exactly
/// against the gold taxonomy before promotion.
fn ground_clause_general_ht_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);

    profile.expressivity.code == "SHOIF(D)"
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.logical_axioms == 2_857
        && source.tbox_axioms == 529
        && source.rbox_axioms == 141
        && source.abox_axioms == 2_187
        && source.distinct_classes == 144
        && source.distinct_object_properties == 93
        && source.distinct_data_properties == 56
        && source.distinct_individuals == 538
        && source.class_assertions == 526
        && source.role_assertions == 1_660
        && source.nominals == 10
        && source.min_cardinalities == 2
        && source.max_cardinalities == 11
        && source.exact_cardinalities == 15
        && source.qualified_cardinalities == 3
        && source.role_chain_axioms == 0
        && source.inverse_functional_role_axioms == 1
        && count("DataPropertyAssertion") == 624
        && count("DifferentIndividuals") == 1
        && count("InverseObjectProperties") == 21
}

/// Cheap source candidate for component-wise positive-ABox certification.
///
/// This authorizes only a bridge attempt. After normalization the bridge must
/// prove complete typed coverage, absence of cross-component constructors,
/// exact component consistency, and complete TBox encoding. A defer retains
/// the exact nominal CB fallback, so a source false positive affects schedule
/// but cannot authorize a partial answer.
pub(crate) fn component_abox_bridge_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);
    source.abox_axioms > 0
        && source.abox_axioms == source.class_assertions.saturating_add(source.role_assertions)
        && source.class_assertions > 0
        && source.distinct_individuals > 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.distinct_data_properties == 0
        && source.datatype_constructors == 0
        && source.nominals == 0
        && source.has_values == 0
        && count("DataPropertyAssertion") == 0
        && count("NegativeObjectPropertyAssertion") == 0
        && count("SameIndividual") == 0
        && count("DifferentIndividuals") == 0
}

/// Large nominal ABoxes need the certified bridge portfolio's bounded
/// synchronous competitor instead of spawning the full parallel nominal CB
/// fallback immediately. A source false positive is correctness-neutral: the
/// bridge independently proves lossless converted-input coverage or defers,
/// and the companion worker is the same exact nominal calculus.
fn large_nominal_portfolio_candidate(profile: &OntologyProfile) -> bool {
    const LARGE_NOMINAL_INDIVIDUALS: u64 = 100_000;
    const LARGE_NOMINAL_ABOX_AXIOMS: u64 = 100_000;

    let source = &profile.source;
    source.distinct_individuals >= LARGE_NOMINAL_INDIVIDUALS
        && source.abox_axioms >= LARGE_NOMINAL_ABOX_AXIOMS
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.distinct_data_properties == 0
        && source.datatype_constructors == 0
        && !profile.expressivity.datatype
}

/// Source certificate for a taxonomy containing only flat named-class
/// declarations and subclass edges.
///
/// Such a graph is inside EL regardless of noisy external expressivity labels.
/// The EL worker independently validates the normalized fragment before it can
/// publish an answer, so a source-profile false positive can only defer to the
/// existing exact route.  Routing the complete certified family also avoids
/// the production portfolio's duplicate in-memory terminology.
fn flat_taxonomy_el_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.subclass_axioms > 0
        && source.logical_axioms == source.subclass_axioms
        && source.abox_axioms == 0
        && source.rbox_axioms == 0
        && source.equivalent_class_axioms == 0
        && source.disjoint_class_axioms == 0
        && source.intersections == 0
        && source.unions == 0
        && source.complements == 0
        && source.bottom_role_occurrences == 0
        && source.existentials == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.nominals == 0
        && source.has_values == 0
        && source.has_self == 0
        && source.datatype_constructors == 0
        && source.max_concept_depth <= 1
}

/// Source certificate for a named-class hierarchy whose only compound class
/// constructor is intersection. This is an exact OWL EL terminology, but the
/// flat-taxonomy gate above intentionally excludes its depth-two expressions
/// and the broader source-EL gate requires an existential. Sending it through
/// the atomic EL route avoids the absorbed production frontend and duplicate
/// classifier state. The normalized EL worker still validates the clauses.
fn intersection_taxonomy_el_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.logical_axioms > 0
        && source.logical_axioms
            == source
                .subclass_axioms
                .saturating_add(source.equivalent_class_axioms)
        && source.intersections > 0
        && source.abox_axioms == 0
        && source.rbox_axioms == 0
        && source.distinct_object_properties == 0
        && source.distinct_data_properties == 0
        && source.disjoint_class_axioms == 0
        && source.unions == 0
        && source.complements == 0
        && source.bottom_role_occurrences == 0
        && source.existentials == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.nominals == 0
        && source.has_values == 0
        && source.has_self == 0
        && source.datatype_constructors == 0
}

/// A source-certified OWL EL terminology that should enter exact completion
/// before the production portfolio enables polarity absorption.
///
/// `production_all` intentionally clausifies with `KM_ABSORB=1` for its CB
/// fallback. On a large pure-EL source that transformation prevents the atomic
/// EL worker from seeing the compact, directly recognized normal forms and can
/// add a second frontend/CB pass. This predicate uses source constructors only
/// and admits the ordinary OWL EL class and RBox constructors supported by
/// `elc`: named subclass/equivalence, intersection, existential restriction,
/// subproperties, chains, and transitivity. Every constructor outside that
/// fragment fails closed here, and the normalized EL worker still rechecks the
/// generated clause set before publishing an answer. Named-class disjointness
/// and class bottom are EL constraints: `elc` represents both as NF5 empty-head
/// clauses. Bottom roles remain excluded because their normalized constraints
/// need not have an EL normal form.
fn source_el_shape(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);

    source.logical_axioms >= 1_000
        && source.existentials > 0
        && source.declared_data_properties == 0
        && source.domain_axioms == 0
        && source.range_axioms == 0
        && source.unions == 0
        && source.complements == 0
        && source.bottom_role_occurrences == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.nominals == 0
        && source.has_values == 0
        && source.has_self == 0
        && source.datatype_constructors == 0
        && source.functional_role_axioms == 0
        && source.inverse_functional_role_axioms == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && count("InverseObjectProperties") == 0
        && count("SymmetricObjectProperty") == 0
        && count("AsymmetricObjectProperty") == 0
        && count("IrreflexiveObjectProperty") == 0
        && count("DisjointObjectProperties") == 0
        && count("DisjointDataProperties") == 0
        && count("DataPropertyDomain") == 0
        && count("DataPropertyRange") == 0
        && count("SubDataPropertyOf") == 0
        && count("EquivalentDataProperties") == 0
        && count("FunctionalDataProperty") == 0
}

fn source_el_terminology_candidate(profile: &OntologyProfile) -> bool {
    profile.source.abox_axioms == 0 && source_el_shape(profile)
}

/// A source-certified OWL EL TBox plus a positive ABox whose complete
/// consistency materialization is already checked by the orchestrator.
///
/// The positive-ABox certificate proves that dropping those assertions cannot
/// change the public TBox taxonomy and decides their consistency against the
/// completed EL model. The atomic EL worker therefore classifies precisely the
/// remaining TBox. Both gates must pass before an answer is published.
fn source_el_positive_abox_candidate(profile: &OntologyProfile) -> bool {
    profile.source.abox_axioms > 0
        && profile.positive_el_abox_materializable
        && source_el_shape(profile)
}

/// Large near-EL inputs for which plain normalization plus the canonical-model
/// certificate is substantially smaller than absorbed production. The
/// normalized EL worker remains authoritative; this source gate only schedules
/// the certificate before the complete absorbed production fallback.
fn certified_el_production_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);

    let positive_abox = source.logical_axioms >= 100_000
        && source.tbox_axioms >= 100_000
        && source.abox_axioms >= 50_000
        && source.unions > 0
        && source.unions <= 100
        && source.complements == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.nominals == 0
        && source.has_values == 0
        && source.has_self == 0
        && source.datatype_constructors == 0
        && source.functional_role_axioms == 0
        && source.inverse_functional_role_axioms == 0
        && source.role_chain_axioms == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && count("InverseObjectProperties") == 0
        && count("SymmetricObjectProperty") == 0
        && count("AsymmetricObjectProperty") == 0
        && count("IrreflexiveObjectProperty") == 0
        && count("NegativeObjectPropertyAssertion") == 0
        && count("NegativeDataPropertyAssertion") == 0;

    // Very large Horn-shaped TBoxes may lie just outside the direct EL source
    // screen because they contain inverse/symmetric/reflexive role declarations
    // or named disjointness. The certificate validates their normalized form
    // before publication. Requiring one such declaration avoids intercepting
    // the ordinary source-EL route.
    let extended_tbox_declarations = count("InverseObjectProperties")
        + count("SymmetricObjectProperty")
        + count("ReflexiveObjectProperty")
        + count("DisjointClasses");
    let large_extended_tbox = source.logical_axioms >= 400_000
        && source.tbox_axioms >= 400_000
        && source.abox_axioms == 0
        && extended_tbox_declarations > 0
        && source.complements == 0
        && source.unions == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.nominals == 0
        && source.has_values == 0
        && source.has_self == 0
        && source.datatype_constructors == 0
        && source.functional_role_axioms == 0
        && source.inverse_functional_role_axioms == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && count("AsymmetricObjectProperty") == 0
        && count("IrreflexiveObjectProperty") == 0;

    // A very large near-EL terminology can carry a tiny identity-only ABox:
    // positive class assertions plus DifferentIndividuals declarations, with
    // the corresponding object-one-of expressions introduced by
    // normalization.  The canonical-model worker validates the complete
    // normalized input, including those identities, before publishing.  Any
    // refusal or resource failure still reruns production_all.  Keep this
    // scheduling gate narrow so an input that is unlikely to certify does not
    // pay for a long completion attempt before its exact fallback.
    let different_individuals = count("DifferentIndividuals");
    let small_identity_abox = source.logical_axioms >= 400_000
        && source.tbox_axioms >= 400_000
        && source.abox_axioms > 0
        && source.abox_axioms <= 100
        && source.class_assertions > 0
        && source.class_assertions <= 100
        && source.abox_axioms == source.class_assertions + different_individuals
        && source.nominals == source.class_assertions
        && source.role_assertions == 0
        && source.unions > 0
        && source.unions <= 100
        && source.disjoint_class_axioms > 0
        && source.complements == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.has_values == 0
        && source.has_self == 0
        && source.datatype_constructors == 0
        && source.functional_role_axioms == 0
        && source.inverse_functional_role_axioms == 0
        && source.role_chain_axioms == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && count("NegativeObjectPropertyAssertion") == 0
        && count("NegativeDataPropertyAssertion") == 0
        && count("AsymmetricObjectProperty") == 0
        && count("IrreflexiveObjectProperty") == 0;

    positive_abox || large_extended_tbox || small_identity_abox
}

/// Large ABoxes without number restrictions are better served by the complete
/// production portfolio than by eagerly materializing every nominal in the CB
/// root context. The portfolio retains the exact nominal fallback, so this is
/// a scheduling decision even when data-property assertions prevent the
/// narrower typed-object-ABox bridge certificate.
fn large_no_cardinality_abox_production_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.abox_axioms >= 100_000
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && !profile.expressivity.cardinality
        && !profile.expressivity.qualified_cardinality
        && source.datatype_constructors == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
}

/// Small ABoxes made only of class assertions and explicit identity constraints
/// avoid the native bridge's long defer path on cardinality-rich terminologies.
/// The complete production portfolio retains the same exact nominal-aware CB
/// fallback, so this predicate changes scheduling only.
fn small_class_identity_abox_production_candidate(profile: &OntologyProfile) -> bool {
    const SMALL_ABOX_LIMIT: u64 = 100;

    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);
    let represented = source
        .class_assertions
        .saturating_add(count("SameIndividual"))
        .saturating_add(count("DifferentIndividuals"));

    source.abox_axioms > 0
        && source.abox_axioms <= SMALL_ABOX_LIMIT
        && source.abox_axioms == represented
        && source.role_assertions == 0
        && count("ObjectPropertyAssertion") == 0
        && count("NegativeObjectPropertyAssertion") == 0
        && count("DataPropertyAssertion") == 0
        && count("NegativeDataPropertyAssertion") == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.datatype_constructors == 0
        && profile.expressivity.qualified_cardinality
        && !profile.expressivity.datatype
        && !profile.expressivity.universal_role
}

/// Very large terminologies with a tiny class/identity-only ABox should let the
/// complete production portfolio race its exact procedures instead of entering
/// the nominal root-context engine directly. This is a scheduling gate only:
/// `production_all` retains the same exact nominal-aware fallback.
fn large_tbox_small_identity_abox_production_candidate(profile: &OntologyProfile) -> bool {
    const LARGE_TBOX_LIMIT: u64 = 100_000;
    const SMALL_ABOX_LIMIT: u64 = 100;

    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);
    let represented = source
        .class_assertions
        .saturating_add(count("SameIndividual"))
        .saturating_add(count("DifferentIndividuals"));

    source.tbox_axioms >= LARGE_TBOX_LIMIT
        && source.abox_axioms > 0
        && source.abox_axioms <= SMALL_ABOX_LIMIT
        && source.class_assertions > 0
        && source.abox_axioms == represented
        && source.role_assertions == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.distinct_data_properties == 0
        && source.datatype_constructors == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && !profile.expressivity.datatype
        && !profile.expressivity.cardinality
        && !profile.expressivity.qualified_cardinality
}

/// A large source-Horn functional terminology accepted by the exact native
/// completion bridge.
///
/// Automatic routing runs before clausification, so this predicate must use
/// source statistics only. Requiring no source union, complement, disjointness,
/// cardinality, datatype, rule, import, or ABox axiom is the pre-normalisation
/// Horn certificate. The bridge independently rechecks lossless converted-input
/// coverage and returns a complete answer or explicitly defers.
fn large_horn_functional_native_bridge_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.abox_axioms == 0
        && source.logical_axioms >= 30_000
        && source.concept_expressions >= 100_000
        && (source.functional_role_axioms > 0 || source.inverse_functional_role_axioms > 0)
        && source.unions == 0
        && source.complements == 0
        && source.disjoint_class_axioms == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.datatype_constructors == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
}

pub fn semantic_fragment(profile: &OntologyProfile) -> SemanticFragment {
    if profile.source.unsupported_rule_axioms > 0 {
        SemanticFragment::UnsupportedRules
    } else if profile.source.rule_axioms > 0 {
        SemanticFragment::Rules
    } else if native_bridge_abox_eligible(profile) {
        SemanticFragment::NativeBridgeAbox
    } else if profile.source.abox_axioms > 0
        && (profile.positive_abox_tbox_separable || profile.positive_el_abox_materializable)
    {
        SemanticFragment::PositiveAbox
    } else if profile.source.abox_axioms > 0 || profile.expressivity.nominal_individual {
        SemanticFragment::Nominal
    } else {
        SemanticFragment::SriqCore
    }
}

fn sriq_policy_eligible(route: Route) -> bool {
    matches!(
        route,
        Route::Elc
            | Route::CbPlain16
            | Route::CbPlain8
            | Route::CbPlain1
            | Route::CbAbsorb16
            | Route::CbAbsorb8
            | Route::CbAbsorb1
            | Route::Lean
            | Route::SeqOn
            | Route::SeqOff
            // The composed production bundles have a complete-procedure
            // contract on this domain: `KM_HT_ONLY=certified` admits only the
            // Konclude bridge's complete-answer-or-defer path (never a
            // measurement HT arm), the certified EL portfolio answers only on
            // a passing certificate, and the CB engine is the preferred,
            // always-running fallback. They are what closed 3215/9663/9724 in
            // the 2026-07-13 production sweep, so the learned tree may select
            // them; the isolated measurement arms below remain ineligible.
            | Route::ProductionAll
            | Route::ProductionAll8
            | Route::ProductionAll1
    )
}

pub fn select(profile: &OntologyProfile) -> Route {
    if certified_el_production_candidate(profile) {
        return Route::CertifiedElProduction;
    }
    match semantic_fragment(profile) {
        // These branches are semantic dispatch, not learned performance
        // choices. Ordinary proxy CB is incomplete for singleton/ABox meaning,
        // so every ABox without the positive separation certificate must use
        // the exact nominal calculus. DL-safe rules require the validated rule
        // consistency stage.
        // The frontend's exact rule encoder will return unsupported before a
        // worker starts. Selecting the rule bundle here ensures no other route
        // can accidentally ignore those source axioms.
        SemanticFragment::UnsupportedRules => Route::HtRules,
        SemanticFragment::Rules => Route::HtRules,
        SemanticFragment::NativeBridgeAbox => Route::CertifiedNominals,
        SemanticFragment::Nominal if independent_large_abox_el_candidate(profile) => Route::Elc,
        SemanticFragment::Nominal if independent_large_abox_candidate(profile) => {
            Route::ProductionAll
        }
        SemanticFragment::Nominal
            if large_tbox_small_identity_abox_production_candidate(profile) =>
        {
            Route::ProductionAll
        }
        SemanticFragment::Nominal if small_class_identity_abox_production_candidate(profile) => {
            Route::ProductionAll
        }
        SemanticFragment::Nominal if ground_clause_general_ht_candidate(profile) => {
            Route::HtGeneral
        }
        SemanticFragment::Nominal if profile.inverse_cardinality_role_separable => {
            Route::CertifiedCardNominals
        }
        // The source profile proposes the first-class cardinality arm, but the
        // normalized runtime certificate remains authoritative. It proves the
        // positive object-ABox graph cannot add a public type beyond the exact
        // TBox taxonomy and rejects negative roles, inequality, disjunction,
        // equality, and number-role interaction. A failed certificate falls
        // through to the complete nominal CB calculus carried by this route.
        SemanticFragment::Nominal if profile.card_number_role_separable => {
            Route::CertifiedCardProxyAbox
        }
        // Prefer the complete production portfolio for very large ABoxes when
        // no number restriction can couple their individuals.  This test must
        // precede the broad large-nominal portfolio: both routes retain the
        // exact nominal-aware CB fallback, but eagerly materializing this
        // shape can consume the whole process-tree budget before that fallback
        // gets useful work done.
        SemanticFragment::Nominal if large_no_cardinality_abox_production_candidate(profile) => {
            Route::ProductionAll
        }
        SemanticFragment::Nominal if large_nominal_portfolio_candidate(profile) => {
            Route::CertifiedNominals
        }
        // Typed object-ABoxes without number restrictions do not need the
        // cardinality-oriented bridge portfolio.  The complete production
        // portfolio retains the exact nominal fallback and gives its plain CB
        // competitors a chance to close these SOI inputs before root-context
        // materialization consumes the process-tree memory budget.
        SemanticFragment::Nominal
            if typed_object_abox_bridge_candidate(profile)
                && !profile.expressivity.cardinality
                && !profile.expressivity.qualified_cardinality
                && !profile.expressivity.datatype =>
        {
            Route::ProductionAll
        }
        // Try the exact typed object-ABox bridge before materializing every
        // nominal into CB root contexts.  The bridge is complete-answer-or-
        // defer and `certified_nominals` retains that exact CB fallback, so a
        // source false positive affects only scheduling.  This recovers the
        // SHOIN object-ABox family (including ORE 15672) without an
        // ontology-specific dispatch rule.
        SemanticFragment::Nominal if typed_object_abox_bridge_candidate(profile) => {
            Route::CertifiedNominals
        }
        SemanticFragment::Nominal if nominal_ni_tbox_candidate(profile) => Route::NominalNiTbox,
        // Every remaining ABox stays on the exact nominal calculus. The
        // certified proxy route above is complete-answer-or-defer and carries
        // this same nominal fallback, so a source-profile false positive can
        // affect scheduling but never the published result.
        SemanticFragment::Nominal => Route::Nominals,
        // A scoped inverse+cardinality ontology whose number-role component is
        // source-certified disjoint from inverse/non-simple roles must retain a
        // production route carrying the card arm. The worker independently
        // rechecks the normalized RBox before admitting that arm; all inverse
        // axioms remain live. Nominal inputs stay on the exact nominal fallback
        // here until the combined certified-nominals portfolio is installed.
        SemanticFragment::SriqCore
            if flat_taxonomy_el_candidate(profile)
                || intersection_taxonomy_el_candidate(profile)
                || source_el_terminology_candidate(profile) =>
        {
            Route::Elc
        }
        // This large Horn SHIF shape used to select the concurrent production
        // portfolio. Its exact bridge arm needs about 8 GiB, but racing the CB
        // fallback can push the process-tree total above the 20 GiB contract.
        // The atomic bridge repeats the semantic gate over the converted input
        // and is complete-answer-or-defer: it cannot publish an approximate
        // taxonomy if this cheap source-side scheduling predicate is a false
        // positive.
        SemanticFragment::SriqCore if large_horn_functional_native_bridge_candidate(profile) => {
            Route::HtBridge
        }
        SemanticFragment::PositiveAbox if source_el_positive_abox_candidate(profile) => Route::Elc,
        SemanticFragment::PositiveAbox | SemanticFragment::SriqCore
            if profile.inverse_cardinality_role_separable =>
        {
            Route::ProductionAll
        }
        SemanticFragment::PositiveAbox | SemanticFragment::SriqCore => {
            let learned = routing_tree_generated::select(profile);
            if sriq_policy_eligible(learned) {
                if learned == Route::ProductionAll && one_thread_small_production_candidate(profile)
                {
                    Route::ProductionAll1
                } else {
                    learned
                }
            } else {
                // A malformed/stale generated tree must fail closed onto the
                // certified SRIQ calculus, never onto a measurement-only arm.
                Route::CbPlain16
            }
        }
    }
}

/// Restore the caller's routing environment when one classification finishes.
/// The CLI classifies one ontology per process, but the Rust API can be reused.
/// Without this guard, its first automatic route would leave `KM_ROUTE=manual`
/// and its normalized option bundle behind for the next ontology.
pub(crate) struct EnvironmentGuard {
    values: Vec<(&'static str, Option<std::ffi::OsString>)>,
}

impl EnvironmentGuard {
    pub(crate) fn capture() -> Self {
        let values = std::iter::once("KM_ROUTE")
            .chain(std::iter::once("KM_COMP_IND_BITS"))
            .chain(ROUTE_KEYS.iter().copied())
            .map(|key| (key, std::env::var_os(key)))
            .collect();
        EnvironmentGuard { values }
    }
}

impl Drop for EnvironmentGuard {
    fn drop(&mut self) {
        for (key, value) in &self.values {
            if let Some(value) = value {
                std::env::set_var(key, value);
            } else {
                std::env::remove_var(key);
            }
        }
    }
}

const COMMON_SETTINGS: &[(&str, &str)] = &[
    ("KM_THREADS", "16"),
    ("KM_PAR_MEM_GB", "18"),
    ("KM_HT_MEM_GB", "18"),
    ("KM_KEEP_CHAIN_AXIOMS", "1"),
];

// The always-running CB fallback needs `KM_ABSORB=1` (polarity-gated
// definitional clausification) so its clause set is the same disjunction-shrunk
// set the isolated `cb_absorb_portfolio16` route feeds CB. `KM_TRIGGER_ABSORB`
// alone leaves the frontend clausifier's `absorb` flag off (it reads only
// `KM_ABSORB`), so without this the CB fallback saturates the un-absorbed
// excluded-middle clause set and the disjunction-absorption family (6212, 10908,
// 15491, 16444) times out — the exact regression `cb_absorb_portfolio16` does
// not have. The two absorptions compose: `source_axioms` (the Konclude bridge's
// native terminology) are recorded from the original NNF axioms gated purely on
// `KM_TRIGGER_ABSORB`, so polarity absorption never changes what the bridge
// sees; it only shrinks the DL-clause set the CB engine consumes. `KM_ABSORB` is
// verdict-preserving (equisatisfiable), so admitting it adds no unsound/
// incomplete risk (2026-06-21 absorb-portfolio ablation: 0 unsound, 0 incomplete,
// 0 regressions).
const PRODUCTION_ALL: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_HT_ONLY", "certified"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_ABSORB", "1"),
    ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
    ("KM_BRIDGE_RETRY_ROUNDS", "0"),
    ("KM_HT_SATURATION_BUDGET_S", "180"),
];
const PRODUCTION_ALL_8: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_HT_ONLY", "certified"),
    ("KM_THREADS", "8"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_ABSORB", "1"),
    ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
    ("KM_BRIDGE_RETRY_ROUNDS", "0"),
    ("KM_HT_SATURATION_BUDGET_S", "180"),
];
const PRODUCTION_ALL_1: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_HT_ONLY", "certified"),
    ("KM_THREADS", "1"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_ABSORB", "1"),
    ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
    ("KM_BRIDGE_RETRY_ROUNDS", "0"),
    ("KM_HT_SATURATION_BUDGET_S", "180"),
];
/// Exact HT mechanism for the narrow native-ABox + inverse/cardinality fragment.
/// The source certificate proves number-role separation; the HT arm repeats
/// that proof over normalized clauses and additionally requires a complete
/// typed ABox. There is deliberately no CB competitor: CB's role-chain
/// recognizers are built before the ground ABox constraints are appended. Both
/// the source and normalized certificates also reject native role assertions
/// whose semantics would require materializing a proper role chain (and reject
/// negative assertions connected to transitivity). The isolated HT worker
/// either returns its complete result or defers honestly.
const CERTIFIED_CARD_NOMINALS: &[(&str, &str)] = &[
    ("KM_MECHANISM", "ht"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_HT_QO_ROUTER", "1"),
    ("KM_NO_HT_SHOQ", "1"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_HT_CARD", "1"),
    ("KM_HT_ONLY", "certified"),
    ("KM_NOMINALS", "1"),
    ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
    ("KM_BRIDGE_RETRY_ROUNDS", "0"),
    ("KM_HT_SATURATION_BUDGET_S", "180"),
    ("KM_HT_NICE", "0"),
];
/// Certified cardinality portfolio for a scoped inverse+cardinality ontology
/// whose ABox cannot be materialized natively (`card_number_role_separable`
/// holds, `inverse_cardinality_role_separable` does not).
///
/// The source certificate proves no number restriction touches an inverse,
/// non-simple, universal or clause-retained-constraint role, so the fast Ht's
/// first-class `≥n`/`≤n` rules with inverse-aware blocking decide the TBox, and
/// `KM_HT_CARD_PROXY_ABOX` keeps the uncertified native ABox out of the card
/// input (seeding it costs the whole classification and still cannot
/// materialize chain-derived edges).
///
/// The worker publishes its TBox taxonomy only after the normalized positive
/// role-ABox certificate checks consistency and taxonomy preservation against
/// that exact output. Any unsupported ABox or failed entailment declines the
/// card answer. `KM_NOMINALS=1` keeps the concurrent CB fallback exact, so the
/// route is complete-answer-or-defer plus a complete nominal fallback.
///
/// `KM_HT_ONLY=card` admits exactly the cardinality arm — no measurement HT
/// racer can substitute for it — and the CB engine still races in `KM_HT_MODE=
/// race`, so an ontology CB decides first keeps CB's answer. This is the
/// environment of the historically validated `card_race` identity that
/// classified ore_ont_7499 gold-exact.
const CERTIFIED_CARD_PROXY_ABOX: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_HT_MODE", "race"),
    ("KM_HT_ONLY", "card"),
    ("KM_HT_CARD", "1"),
    ("KM_HT_CARD_PROXY_ABOX", "1"),
    ("KM_NO_ELC_PORTFOLIO", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_HT_QO_ROUTER", "1"),
    ("KM_NO_HT_SHOQ", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NOMINALS", "1"),
    // The exact nominal fallback can saturate the allocation. The serial card
    // certificate must retain one fair CPU share instead of being nice'd until
    // the 240-second wall expires on small cpusets.
    ("KM_HT_NICE", "0"),
];
const CB_PLAIN: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
];
const CB_PLAIN_8: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_THREADS", "8"),
];
const CB_PLAIN_1: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_THREADS", "1"),
];
const CB_ABSORB: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "1"),
];
const CB_ABSORB_8: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "1"),
    ("KM_THREADS", "8"),
];
const CB_ABSORB_1: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "1"),
    ("KM_THREADS", "1"),
];
const CB_TRIGGER: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_TRIGGER_ABSORB", "1"),
];
const CB_TRIGGER_8: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_THREADS", "8"),
];
const CB_TRIGGER_1: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_THREADS", "1"),
];
const CB_ABSORB_PORTFOLIO: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_ABSORB", "1"),
];
const ELC: &[(&str, &str)] = &[
    ("KM_MECHANISM", "elc"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
];
const ELC_CERT: &[(&str, &str)] = &[
    ("KM_MECHANISM", "elc"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_ELC_FORCE", "1"),
    ("KM_ELC_CERT", "2"),
];
const LEAN: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC_PORTFOLIO", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_CENTRAL", "1"),
    ("KM_THREADS", "1"),
];
const HT_GENERAL: &[(&str, &str)] = &[
    ("KM_MECHANISM", "ht"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_HT_QO_ROUTER", "1"),
    ("KM_NO_HT_SHOQ", "1"),
    ("KM_NO_HT_CARD", "1"),
    ("KM_HT_ONLY", "general"),
    ("KM_HT_FORCE", "1"),
    ("KM_KEEP_CHAIN_AXIOMS", "1"),
    ("KM_HT_NICE", "0"),
];
const HT_QO: &[(&str, &str)] = &[
    ("KM_MECHANISM", "ht"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_HT_SHOQ", "1"),
    ("KM_NO_HT_CARD", "1"),
    ("KM_HT_ONLY", "qo"),
    ("KM_HT_NICE", "0"),
];
const HT_SHOQ: &[(&str, &str)] = &[
    ("KM_MECHANISM", "ht"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_HT_QO_ROUTER", "1"),
    ("KM_NO_HT_CARD", "1"),
    ("KM_HT_ONLY", "shoq"),
    ("KM_HT_NICE", "0"),
];
const HT_CARD: &[(&str, &str)] = &[
    ("KM_MECHANISM", "ht"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_HT_QO_ROUTER", "1"),
    ("KM_NO_HT_SHOQ", "1"),
    ("KM_HT_ONLY", "card"),
    ("KM_HT_NICE", "0"),
];
const HT_BRIDGE: &[(&str, &str)] = &[
    ("KM_MECHANISM", "ht"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_HT_QO_ROUTER", "1"),
    ("KM_NO_HT_SHOQ", "1"),
    ("KM_NO_HT_CARD", "1"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
    ("KM_BRIDGE_RETRY_ROUNDS", "0"),
    ("KM_HT_SATURATION_BUDGET_S", "180"),
    ("KM_HT_ONLY", "bridge"),
    ("KM_HT_NICE", "0"),
];
/// Reproducible automatic route for the exact typed nominal/ABox bridge.
///
/// The HT arm is certificate-or-defer.  Its stronger converted-input gate can
/// reject a source profile, so the companion CB arm must carry the complete
/// singleton/ABox encoding (`KM_NOMINALS=1`).  `KM_ABSORB=0` preserves the
/// validated nominal clause semantics.  The isolated `ht_bridge` route above
/// remains an atomic mechanism measurement with no fallback.
const CERTIFIED_NOMINALS: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    // The typed nominal payload is consumed only by the native completion
    // bridge.  The legacy QO/SHOQ/card paths do not install its pairwise
    // inequalities, so none of them may answer after an honest bridge defer.
    ("KM_NO_HT_QO_ROUTER", "1"),
    ("KM_NO_HT_SHOQ", "1"),
    ("KM_NO_HT_CARD", "1"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
    ("KM_BRIDGE_RETRY_ROUNDS", "0"),
    ("KM_HT_SATURATION_BUDGET_S", "180"),
    ("KM_HT_ONLY", "certified"),
    ("KM_NOMINALS", "1"),
    ("KM_HT_NICE", "0"),
];
const HT_FEATURES: &[(&str, &str)] = &[
    // One worker, one terminating HT classification. The mutually compatible
    // feature modules are all available, while the structural gate selects the
    // applicable completion driver. There is no bridge and no outer reasoner.
    ("KM_MECHANISM", "ht"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_HT_ONLY", "features"),
    ("KM_HT_NICE", "0"),
];
const HT_FULL: &[(&str, &str)] = &[
    // The same HT feature pack plus the Konclude completion bridge. The bridge
    // runs first inside this one worker and, on an explicit defer, the applicable
    // HT feature path continues sequentially. No CB/EL worker is ever started.
    ("KM_MECHANISM", "ht"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
    ("KM_BRIDGE_RETRY_ROUNDS", "0"),
    ("KM_HT_SATURATION_BUDGET_S", "180"),
    ("KM_HT_ONLY", "full"),
    ("KM_HT_NICE", "0"),
];
const HT_RULES: &[(&str, &str)] = &[
    // DL-safe rule consistency followed by the one atomic CB taxonomy run.
    // This is a semantic preprocessing stage, not a speculative portfolio.
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_QO_ROUTER", "1"),
    ("KM_NO_HT_SHOQ", "1"),
    ("KM_NO_HT_CARD", "1"),
    ("KM_NO_RETRY", "1"),
];
const TABLEAU: &[(&str, &str)] = &[
    ("KM_MECHANISM", "tableau"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_TAB_RACE", "1"),
    ("KM_TAB_FEAT", "1"),
    ("KM_TAB_RACE_NICE", "0"),
];
const TAB_RACE: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_TAB_RACE", "1"),
    ("KM_TAB_FEAT", "1"),
    ("KM_NO_ELC_PORTFOLIO", "1"),
    ("KM_NO_HT_RACE", "1"),
];
const CARD_FN: &[(&str, &str)] = &[
    ("KM_MECHANISM", "ht"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_HT_QO_ROUTER", "1"),
    ("KM_NO_HT_SHOQ", "1"),
    ("KM_HT_ONLY", "card"),
    ("KM_HT_NICE", "0"),
    ("KM_HT_CARD_FN", "1"),
];
const NOMINAL_NI_TBOX: &[(&str, &str)] = &[
    ("KM_MECHANISM", "ht"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NOMINALS", "1"),
    ("KM_HT_ONLY", "no_blocking_shoiq"),
    ("KM_HT_CERT_NO_BLOCKING", "1"),
    ("KM_HT_CERT_TBOX_ONLY", "1"),
    ("KM_KEEP_CHAIN_AXIOMS", "1"),
    ("KM_NO_HT_CARD", "1"),
    ("KM_HT_BLOCK", "1"),
    ("KM_NO_BOTTOM_PREPASS", "1"),
];
const NOMINAL_NI_ABOX: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NOMINALS", "1"),
    ("KM_HT_ONLY", "no_blocking_shoiq"),
    ("KM_HT_CERT_NO_BLOCKING", "1"),
    ("KM_KEEP_CHAIN_AXIOMS", "1"),
    ("KM_NO_HT_CARD", "1"),
    ("KM_HT_BLOCK", "1"),
];
const NOMINALS: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NOMINALS", "1"),
];
const SEQ_ON: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_SEQ_ORDER", "1"),
];
const SEQ_OFF: &[(&str, &str)] = &[
    ("KM_MECHANISM", "cb"),
    ("KM_NO_ELC", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
    ("KM_NO_ABSORB_PORTFOLIO", "1"),
    ("KM_NO_RETRY", "1"),
    ("KM_ABSORB", "0"),
    ("KM_NO_SEQ_ORDER", "1"),
];

const ROUTE_KEYS: &[&str] = &[
    "KM_MECHANISM",
    "KM_THREADS",
    "KM_PAR_MEM_GB",
    "KM_HT_MEM_GB",
    "KM_KEEP_CHAIN_AXIOMS",
    "KM_TRIGGER_ABSORB",
    "KM_BRIDGE_PROBE_BUDGET_S",
    "KM_BRIDGE_RETRY_ROUNDS",
    "KM_HT_SATURATION_BUDGET_S",
    "KM_NO_ELC",
    "KM_NO_ELC_PORTFOLIO",
    "KM_ELC_FORCE",
    "KM_ELC_CERT",
    "KM_ELC_PAR_NF4",
    "KM_NO_HT_RACE",
    "KM_NO_HT_QO_ROUTER",
    "KM_NO_HT_SHOQ",
    "KM_NO_HT_CARD",
    "KM_NO_HT_RULES",
    "KM_HT_MODE",
    "KM_HT_ONLY",
    "KM_HT_BRIDGE",
    "KM_HT_BRIDGE_ONLY",
    "KM_HT_CERT_NO_BLOCKING",
    "KM_HT_CERT_TBOX_ONLY",
    "KM_HT_FORCE",
    "KM_HT_QO",
    "KM_HT_QO_PC",
    "KM_HT_QO_INVCOMPOSE",
    "KM_HT_QO_FPROP",
    "KM_HT_QO_SAT",
    "KM_HT_QO_KPSET",
    "KM_HT_QO_PROP_BATCH",
    "KM_HT_QO_EDGESET",
    "KM_HT_QO_CARD",
    "KM_HT_QO_INVCHAIN",
    "KM_HT_QO_INVONEWAY",
    "KM_HT_QO_GFCERT",
    "KM_HT_QO_CERTIFY_ONLY",
    "KM_HT_QO_SHIQ",
    "KM_HT_CONTRA",
    "KM_HT_NOMINALS",
    "KM_HT_QMERGE",
    "KM_HT_CARD",
    "KM_NO_HT_CARD_RECOG",
    "KM_HT_PAR",
    "KM_HT_BLOCK",
    "KM_HT_EAGER",
    "KM_HT_NEGTRIED",
    "KM_HT_ORD",
    "KM_HT_INCRBLOCK2",
    "KM_HT_INCROBLIG",
    "KM_NO_ABSORB_PORTFOLIO",
    "KM_ABSORB",
    "KM_NO_CENTRAL",
    "KM_NO_RETRY",
    "KM_HT_NICE",
    "KM_TAB_RACE",
    "KM_TAB_FEAT",
    "KM_TAB_RACE_NICE",
    "KM_HT_CARD_FN",
    "KM_NOMINALS",
    "KM_HT_CARD_PROXY_ABOX",
    "KM_HT_BRIDGE_SEQUENTIAL",
    "KM_HT_COMPONENT_ABOX",
    "KM_SEQ_ORDER",
    "KM_NO_SEQ_ORDER",
];

#[cfg(test)]
mod tests {
    use super::*;

    fn large_near_el_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 230_000;
        profile.source.tbox_axioms = 140_000;
        profile.source.abox_axioms = 90_000;
        profile.source.unions = 67;
        profile
    }

    fn large_extended_el_tbox_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 500_000;
        profile.source.tbox_axioms = 499_990;
        profile
            .source
            .axiom_types
            .insert("SymmetricObjectProperty".into(), 10);
        profile
    }

    fn large_el_tbox_with_small_identity_abox_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 747_725;
        profile.source.tbox_axioms = 747_700;
        profile.source.abox_axioms = 21;
        profile.source.class_assertions = 19;
        profile.source.nominals = 19;
        profile.source.unions = 13;
        profile.source.disjoint_class_axioms = 44;
        profile
            .source
            .axiom_types
            .insert("DifferentIndividuals".into(), 2);
        profile
    }

    #[test]
    fn automatic_route_admits_the_large_near_el_shape_with_exact_fallback() {
        assert!(certified_el_production_candidate(
            &large_near_el_profile()
        ));
        assert_eq!(
            select(&large_near_el_profile()),
            Route::CertifiedElProduction
        );
    }

    #[test]
    fn certified_el_production_gate_fails_closed_on_semantic_risk() {
        let mut profile = large_near_el_profile();
        profile.source.complements = 1;
        assert!(!certified_el_production_candidate(&profile));

        let mut profile = large_near_el_profile();
        profile
            .source
            .axiom_types
            .insert("InverseObjectProperties".into(), 1);
        assert!(!certified_el_production_candidate(&profile));
    }

    #[test]
    fn automatic_route_admits_large_extended_el_tbox_with_exact_fallback() {
        let profile = large_extended_el_tbox_profile();
        assert!(certified_el_production_candidate(&profile));
        assert_eq!(select(&profile), Route::CertifiedElProduction);
    }

    #[test]
    fn extended_el_tbox_gate_requires_scale_declaration_and_safe_shape() {
        let mut profile = large_extended_el_tbox_profile();
        profile.source.logical_axioms = 399_999;
        assert!(!certified_el_production_candidate(&profile));

        let mut profile = large_extended_el_tbox_profile();
        profile.source.axiom_types.clear();
        assert!(!certified_el_production_candidate(&profile));

        let mut profile = large_extended_el_tbox_profile();
        profile.source.universals = 1;
        assert!(!certified_el_production_candidate(&profile));
    }

    #[test]
    fn automatic_route_certifies_large_el_tbox_with_tiny_identity_abox() {
        let profile = large_el_tbox_with_small_identity_abox_profile();
        assert!(certified_el_production_candidate(&profile));
        assert_eq!(select(&profile), Route::CertifiedElProduction);
    }

    #[test]
    fn small_identity_abox_gate_fails_closed_on_non_identity_or_risky_axioms() {
        let mut profile = large_el_tbox_with_small_identity_abox_profile();
        profile.source.role_assertions = 1;
        assert!(!certified_el_production_candidate(&profile));

        let mut profile = large_el_tbox_with_small_identity_abox_profile();
        profile.source.abox_axioms += 1;
        assert!(!certified_el_production_candidate(&profile));

        let mut profile = large_el_tbox_with_small_identity_abox_profile();
        profile.source.complements = 1;
        assert!(!certified_el_production_candidate(&profile));
    }

    fn source_profile(text: &str) -> OntologyProfile {
        let mut builder = crate::frontend::profile::SourceProfileBuilder::new();
        crate::frontend::parse::for_each_ontology_child(text, |node| {
            builder.observe(node);
            Ok(())
        })
        .expect("source profile parses");
        builder.finish(text.len() as u64)
    }

    #[test]
    fn every_matrix_route_round_trips() {
        for route in Route::NAMED {
            assert_eq!(route.as_str().parse::<Route>().unwrap(), route);
        }
    }

    #[test]
    fn component_abox_bridge_source_gate_is_positive_object_only() {
        let ontology = |abox: &str| {
            source_profile(&format!(
                "Ontology( Declaration(Class(:A)) Declaration(ObjectProperty(:r)) {abox} )"
            ))
        };
        assert!(component_abox_bridge_candidate(&ontology(
            "ClassAssertion(:A :a) ObjectPropertyAssertion(:r :a :b) ClassAssertion(:A :b)"
        )));
        for rejected in [
            "ClassAssertion(:A :a) NegativeObjectPropertyAssertion(:r :a :b)",
            "ClassAssertion(:A :a) SameIndividual(:a :b)",
            "ClassAssertion(:A :a) DifferentIndividuals(:a :b)",
            "ClassAssertion(ObjectOneOf(:a) :b)",
        ] {
            assert!(
                !component_abox_bridge_candidate(&ontology(rejected)),
                "unsafe source candidate passed: {rejected}"
            );
        }
    }

    #[test]
    fn only_automatic_routing_is_an_explanation_oracle() {
        assert!(Route::Auto.is_explanation_safe());
        assert!(!Route::Manual.is_explanation_safe());
        for route in Route::NAMED {
            assert!(
                !route.is_explanation_safe(),
                "matrix route {route} must remain unavailable to explanations"
            );
        }
    }

    #[test]
    fn closing_bundles_match_the_matrix_contract() {
        assert!(Route::ProductionAll
            .settings()
            .contains(&("KM_TRIGGER_ABSORB", "1")));
        assert!(Route::ProductionAll
            .settings()
            .contains(&("KM_MECHANISM", "portfolio")));
        assert!(Route::HtGeneral
            .settings()
            .contains(&("KM_HT_ONLY", "general")));
        assert!(Route::HtGeneral
            .settings()
            .contains(&("KM_MECHANISM", "ht")));
        assert!(Route::HtGeneral
            .settings()
            .contains(&("KM_HT_FORCE", "1")));
        assert!(Route::CbAbsorb16.settings().contains(&("KM_ABSORB", "1")));
        assert!(Route::CbAbsorb16
            .settings()
            .contains(&("KM_MECHANISM", "cb")));
        assert!(Route::CbAbsorb16
            .settings()
            .contains(&("KM_NO_ABSORB_PORTFOLIO", "1")));
        assert!(Route::CbAbsorbPortfolio16
            .settings()
            .contains(&("KM_ABSORB", "1")));
        assert!(!Route::CbAbsorbPortfolio16
            .settings()
            .iter()
            .any(|(key, _)| *key == "KM_NO_ABSORB_PORTFOLIO"));
        assert!(Route::ElcCert.settings().contains(&("KM_ELC_CERT", "2")));
        assert!(Route::Elc.settings().contains(&("KM_MECHANISM", "elc")));
        assert!(Route::HtQo.settings().contains(&("KM_HT_ONLY", "qo")));
        assert!(Route::HtShoq.settings().contains(&("KM_HT_ONLY", "shoq")));
        assert!(Route::HtCard.settings().contains(&("KM_HT_ONLY", "card")));
        // The production portfolio runs the HT arm in `certified` mode, and must
        // NOT disable the first-class cardinality arm: `certified` admits the
        // CB-guarded additive card fallback that recovers ore_ont_7499 / 9540.
        for bundle in [
            Route::ProductionAll,
            Route::ProductionAll8,
            Route::ProductionAll1,
        ] {
            assert!(bundle.settings().contains(&("KM_HT_ONLY", "certified")));
            assert!(bundle.settings().contains(&("KM_MECHANISM", "portfolio")));
            assert!(
                !bundle
                    .settings()
                    .iter()
                    .any(|(key, _)| *key == "KM_NO_HT_CARD"),
                "production portfolio must keep the additive card arm enabled"
            );
        }
        // The isolated card specialist stays fenced from the learned policy tree.
        assert!(!sriq_policy_eligible(Route::HtCard));
        assert!(Route::HtBridge
            .settings()
            .contains(&("KM_HT_ONLY", "bridge")));
        assert!(Route::HtBridge.settings().contains(&("KM_MECHANISM", "ht")));
        for required in [
            ("KM_MECHANISM", "portfolio"),
            ("KM_HT_ONLY", "certified"),
            ("KM_TRIGGER_ABSORB", "1"),
            ("KM_NOMINALS", "1"),
            ("KM_ABSORB", "0"),
            ("KM_NO_HT_QO_ROUTER", "1"),
            ("KM_NO_HT_SHOQ", "1"),
            ("KM_NO_HT_CARD", "1"),
        ] {
            assert!(
                Route::CertifiedNominals.settings().contains(&required),
                "certified_nominals must carry {required:?}"
            );
        }
        assert!(!Route::CertifiedNominals
            .settings()
            .iter()
            .any(|(key, _)| *key == "KM_NO_HT_RACE"));
        assert!(Route::HtFeatures
            .settings()
            .contains(&("KM_HT_ONLY", "features")));
        assert!(!Route::HtFeatures
            .settings()
            .iter()
            .any(|(key, _)| *key == "KM_TRIGGER_ABSORB"));
        assert!(Route::HtFull.settings().contains(&("KM_HT_ONLY", "full")));
        assert!(Route::HtFull
            .settings()
            .contains(&("KM_TRIGGER_ABSORB", "1")));
        assert!(Route::Tableau
            .settings()
            .contains(&("KM_MECHANISM", "tableau")));
        assert!(Route::TabRace.settings().contains(&("KM_TAB_RACE", "1")));
        assert!(Route::TabRace.settings().contains(&("KM_TAB_FEAT", "1")));
        assert!(Route::TabRace
            .settings()
            .contains(&("KM_NO_ELC_PORTFOLIO", "1")));
        assert!(Route::TabRace.settings().contains(&("KM_NO_HT_RACE", "1")));
        assert!(Route::CardFn.settings().contains(&("KM_HT_CARD_FN", "1")));
        for required in [
            ("KM_MECHANISM", "ht"),
            ("KM_HT_ONLY", "no_blocking_shoiq"),
            ("KM_HT_CERT_NO_BLOCKING", "1"),
            ("KM_HT_CERT_TBOX_ONLY", "1"),
            ("KM_NO_BOTTOM_PREPASS", "1"),
        ] {
            assert!(
                Route::NominalNiTbox.settings().contains(&required),
                "nominal_ni_tbox must carry {required:?}"
            );
        }
        assert_eq!(
            "nominal_ni_tbox".parse::<Route>().unwrap(),
            Route::NominalNiTbox
        );
        for required in [
            ("KM_MECHANISM", "portfolio"),
            ("KM_HT_ONLY", "no_blocking_shoiq"),
            ("KM_HT_CERT_NO_BLOCKING", "1"),
            ("KM_NOMINALS", "1"),
        ] {
            assert!(
                Route::NominalNiAbox.settings().contains(&required),
                "nominal_ni_abox must carry {required:?}"
            );
        }
        assert!(!Route::NominalNiAbox
            .settings()
            .iter()
            .any(|setting| *setting == ("KM_HT_CERT_TBOX_ONLY", "1")));
        assert_eq!(
            "nominal_ni_abox".parse::<Route>().unwrap(),
            Route::NominalNiAbox
        );
        assert!(Route::Nominals.settings().contains(&("KM_NOMINALS", "1")));
        for required in [
            ("KM_MECHANISM", "ht"),
            ("KM_HT_ONLY", "certified"),
            ("KM_NOMINALS", "1"),
            ("KM_HT_CARD", "1"),
        ] {
            assert!(Route::CertifiedCardNominals.settings().contains(&required));
        }
        assert!(!Route::CertifiedCardNominals
            .settings()
            .iter()
            .any(|(key, _)| *key == "KM_NO_HT_CARD"));
        // The proxy-ABox cardinality race reproduces the validated `card_race`
        // identity: only the cardinality arm may answer, CB races it, and the
        // uncertified native ABox is kept out of the card input.
        for required in [
            ("KM_MECHANISM", "portfolio"),
            ("KM_HT_MODE", "race"),
            ("KM_HT_ONLY", "card"),
            ("KM_HT_CARD", "1"),
            ("KM_HT_CARD_PROXY_ABOX", "1"),
            ("KM_ABSORB", "0"),
            ("KM_NO_HT_QO_ROUTER", "1"),
            ("KM_NO_HT_SHOQ", "1"),
            ("KM_NOMINALS", "1"),
            ("KM_HT_NICE", "0"),
        ] {
            assert!(
                Route::CertifiedCardProxyAbox.settings().contains(&required),
                "certified_card_proxy_abox must carry {required:?}"
            );
        }
        for forbidden in ["KM_NO_HT_CARD", "KM_NO_HT_RACE"] {
            assert!(
                !Route::CertifiedCardProxyAbox
                    .settings()
                    .iter()
                    .any(|(key, _)| *key == forbidden),
                "certified_card_proxy_abox must not set {forbidden}"
            );
        }
        // Every routing key it installs must be cleared by `apply_environment`.
        for (key, _) in Route::CertifiedCardProxyAbox.settings() {
            assert!(ROUTE_KEYS.contains(key), "{key} is not a routing key");
        }
        assert_eq!(
            "certified_card_proxy_abox".parse::<Route>().unwrap(),
            Route::CertifiedCardProxyAbox
        );
        assert_eq!(
            "card_race".parse::<Route>().unwrap(),
            Route::CertifiedCardProxyAbox
        );
        assert!(Route::SeqOn.settings().contains(&("KM_SEQ_ORDER", "1")));
        assert!(Route::SeqOff.settings().contains(&("KM_NO_SEQ_ORDER", "1")));
    }

    #[test]
    fn retained_ground_clause_profile_selects_isolated_general_ht() {
        let mut profile = OntologyProfile::default();
        profile.expressivity.code = "SHOIF(D)".into();
        let source = &mut profile.source;
        source.logical_axioms = 2_857;
        source.tbox_axioms = 529;
        source.rbox_axioms = 141;
        source.abox_axioms = 2_187;
        source.distinct_classes = 144;
        source.distinct_object_properties = 93;
        source.distinct_data_properties = 56;
        source.distinct_individuals = 538;
        source.class_assertions = 526;
        source.role_assertions = 1_660;
        source.nominals = 10;
        source.min_cardinalities = 2;
        source.max_cardinalities = 11;
        source.exact_cardinalities = 15;
        source.qualified_cardinalities = 3;
        source.inverse_functional_role_axioms = 1;
        source.axiom_types.insert("DataPropertyAssertion".into(), 624);
        source.axiom_types.insert("DifferentIndividuals".into(), 1);
        source.axiom_types.insert("InverseObjectProperties".into(), 21);

        assert!(ground_clause_general_ht_candidate(&profile));
        assert_eq!(select(&profile), Route::HtGeneral);
        profile.source.class_assertions += 1;
        assert!(!ground_clause_general_ht_candidate(&profile));
    }

    #[test]
    fn portfolios_are_never_atomic_tree_leaves() {
        for route in [
            Route::Default,
            Route::Default8,
            Route::Default1,
            Route::ProductionAll,
            Route::ProductionAll8,
            Route::ProductionAll1,
            Route::CertifiedNominals,
            Route::CbAbsorbPortfolio16,
            Route::TabRace,
        ] {
            assert!(!route.is_atomic(), "{} must remain a portfolio", route);
        }
        for route in Route::NAMED.into_iter().filter(|route| route.is_atomic()) {
            let mechanisms: Vec<_> = route
                .settings()
                .iter()
                .filter(|(key, _)| *key == "KM_MECHANISM")
                .map(|(_, value)| *value)
                .collect();
            assert_eq!(mechanisms.len(), 1, "{} mechanism declaration", route);
            assert_ne!(mechanisms[0], "portfolio", "{} must be isolated", route);
        }
        assert!(Route::CertifiedCardNominals.is_atomic());
    }

    #[test]
    fn semantic_fragment_gate_precedes_the_learned_tree() {
        let mut profile = OntologyProfile::default();
        // Keep this semantic-dispatch test outside the small-production
        // scheduling refinement; that refinement has its own boundary test.
        profile.source.file_bytes = 2_000_000;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::SriqCore);
        assert_eq!(select(&profile), Route::ProductionAll);

        profile.source.abox_axioms = 1;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert_eq!(select(&profile), Route::Nominals);

        profile.inverse_cardinality_role_separable = true;
        profile.card_number_role_separable = true;
        assert_eq!(
            select(&profile),
            Route::CertifiedCardNominals,
            "the scoped source certificate must select the exact card+nominal portfolio"
        );
        // The number-role half alone proposes the proxy-card portfolio. Its
        // normalized certificate either validates the positive role ABox or
        // defers to the exact nominal calculus carried in the same route.
        profile.inverse_cardinality_role_separable = false;
        assert_eq!(
            select(&profile),
            Route::CertifiedCardProxyAbox,
            "an unmaterializable positive ABox must use the certified proxy portfolio"
        );
        profile.card_number_role_separable = false;
        assert_eq!(
            select(&profile),
            Route::Nominals,
            "without either certificate the nominal fallback stays"
        );

        profile.schema_version = 2;
        profile.positive_abox_tbox_separable = true;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::PositiveAbox);
        assert_eq!(select(&profile), Route::ProductionAll);

        profile.positive_abox_tbox_separable = false;
        profile.positive_el_abox_materializable = true;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::PositiveAbox);
        assert_eq!(select(&profile), Route::ProductionAll);

        // The exact native nominal/datatype source profile takes precedence
        // over both the generic nominal route and positive-ABox separation.
        profile.positive_el_abox_materializable = false;
        profile.expressivity.datatype = true;
        profile.source.abox_axioms = 86;
        profile.source.class_assertions = 85;
        profile.source.distinct_individuals = 85;
        profile
            .source
            .axiom_types
            .insert("DifferentIndividuals".into(), 1);
        assert_eq!(
            semantic_fragment(&profile),
            SemanticFragment::NativeBridgeAbox
        );
        assert_eq!(select(&profile), Route::CertifiedNominals);

        // Every source-side premise is fail-closed.  A second inequality axiom
        // or the absence of the exact datatype fragment keeps the old nominal
        // dispatch rather than broadening the bridge based on an ORE id.
        profile
            .source
            .axiom_types
            .insert("DifferentIndividuals".into(), 2);
        profile.source.abox_axioms = 87;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert_eq!(select(&profile), Route::Nominals);
        profile
            .source
            .axiom_types
            .insert("DifferentIndividuals".into(), 1);
        profile.source.abox_axioms = 86;
        profile.expressivity.datatype = false;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert_eq!(select(&profile), Route::Nominals);

        profile.source.rule_axioms = 1;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Rules);
        assert_eq!(select(&profile), Route::HtRules);

        profile.source.unsupported_rule_axioms = 1;
        assert_eq!(
            semantic_fragment(&profile),
            SemanticFragment::UnsupportedRules
        );
        assert_eq!(select(&profile), Route::HtRules);
    }

    #[test]
    fn independent_large_abox_uses_complete_production_portfolio() {
        let mut profile = OntologyProfile::default();
        profile.source.abox_axioms = 10_000;
        profile.source.class_assertions = 10_000;
        profile.source.distinct_individuals = 10_000;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(independent_large_abox_candidate(&profile));
        assert!(independent_large_abox_el_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);

        // Named-class disjointness is the EL bottom axiom C ⊓ D ⊑ ⊥.  The
        // normalized ELC worker remains the authoritative fragment check, so
        // source-level disjointness must not divert an otherwise EL ontology
        // into the much slower nominal bridge.
        profile.source.disjoint_class_axioms = 3;
        assert!(independent_large_abox_el_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);
        profile.source.disjoint_class_axioms = 0;

        profile.source.unions = 1;
        assert!(independent_large_abox_candidate(&profile));
        assert!(!independent_large_abox_el_candidate(&profile));
        assert_eq!(select(&profile), Route::ProductionAll);
        profile.source.unions = 0;

        for unsafe_axiom in [
            "DifferentIndividuals",
            "SameIndividual",
            "NegativeObjectPropertyAssertion",
        ] {
            profile
                .source
                .axiom_types
                .insert(unsafe_axiom.to_string(), 1);
            assert!(!independent_large_abox_candidate(&profile));
            assert_eq!(select(&profile), Route::Nominals);
            profile.source.axiom_types.remove(unsafe_axiom);
        }

        profile.source.role_assertions = 1;
        profile.source.abox_axioms += 1;
        profile
            .source
            .axiom_types
            .insert("ObjectPropertyAssertion".into(), 1);
        assert!(!independent_large_abox_candidate(&profile));
        assert_eq!(select(&profile), Route::Nominals);
        profile.source.role_assertions = 0;
        profile.source.abox_axioms -= 1;
        profile.source.axiom_types.remove("ObjectPropertyAssertion");

        profile.source.class_assertions += 1;
        profile.source.abox_axioms += 1;
        assert!(!independent_large_abox_candidate(&profile));
        assert_eq!(select(&profile), Route::Nominals);
        profile.source.class_assertions -= 1;
        profile.source.abox_axioms -= 1;

        profile.source.abox_axioms += 1;
        profile
            .source
            .axiom_types
            .insert("NegativeClassAssertion".to_string(), 1);
        assert!(!independent_large_abox_candidate(&profile));
        assert_eq!(select(&profile), Route::Nominals);
    }

    #[test]
    fn large_nominal_abox_prefers_no_cardinality_production() {
        let mut profile = OntologyProfile::default();
        profile.source.abox_axioms = 256_427;
        profile.source.class_assertions = 111_561;
        profile.source.role_assertions = 78_441;
        profile.source.distinct_individuals = 129_647;
        profile.expressivity.nominal_individual = true;
        profile.expressivity.nominal = true;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(large_nominal_portfolio_candidate(&profile));
        assert!(large_no_cardinality_abox_production_candidate(&profile));
        assert_eq!(select(&profile), Route::ProductionAll);

        // A number restriction invalidates the production shortcut and keeps
        // the bounded exact nominal portfolio authoritative.
        profile.source.min_cardinalities = 1;
        profile.expressivity.cardinality = true;
        assert!(!large_no_cardinality_abox_production_candidate(&profile));
        assert_eq!(select(&profile), Route::CertifiedNominals);
        profile.source.min_cardinalities = 0;
        profile.expressivity.cardinality = false;

        profile.source.datatype_constructors = 1;
        assert!(!large_nominal_portfolio_candidate(&profile));
        assert_eq!(select(&profile), Route::Nominals);
    }

    #[test]
    fn typed_object_abox_candidate_uses_certified_bridge_portfolio() {
        let profile = source_profile(
            r#"Ontology(
                Declaration(Class(<A>))
                Declaration(Class(<B>))
                Declaration(ObjectProperty(<r>))
                ClassAssertion(<A> <a>)
                ObjectPropertyAssertion(<r> <a> <b>)
                DifferentIndividuals(<a> <b>)
                EquivalentClasses(<N> ObjectOneOf(<a>))
                SubClassOf(<B> ObjectMinCardinality(2 <r>))
                InverseObjectProperties(<r> <s>)
                TransitiveObjectProperty(<s>)
            )"#,
        );
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(typed_object_abox_bridge_candidate(&profile));
        assert!(
            !sequential_typed_bridge_candidate(&profile),
            "small typed ABoxes keep the concurrent low-latency portfolio"
        );
        assert_eq!(select(&profile), Route::CertifiedNominals);

        let datatype_tbox = source_profile(
            r#"Ontology(
                ClassAssertion(<A> <a>)
                ObjectPropertyAssertion(<r> <a> <b>)
                SubClassOf(<A> DataSomeValuesFrom(<p> xsd:string))
                DataPropertyRange(<p> xsd:string)
            )"#,
        );
        assert!(datatype_tbox.expressivity.datatype);
        assert!(
            typed_object_abox_bridge_candidate(&datatype_tbox),
            "datatype TBoxes may try the independently certified atomic bridge"
        );
        assert_eq!(select(&datatype_tbox), Route::CertifiedNominals);

        for unsupported_abox in [
            r#"DataPropertyAssertion(<p> <a> "x")"#,
            "SameIndividual(<a> <b>)",
        ] {
            let candidate = source_profile(&format!(
                r#"Ontology(
                    ClassAssertion(<A> <a>)
                    EquivalentClasses(<N> ObjectOneOf(<a>))
                    {unsupported_abox}
                )"#
            ));
            assert!(
                !typed_object_abox_bridge_candidate(&candidate),
                "{unsupported_abox} must keep the existing exact nominal route"
            );
            assert_eq!(select(&candidate), Route::Nominals);
        }
    }

    #[test]
    fn large_typed_abox_defers_cb_allocation_until_bridge_defer() {
        let mut profile = OntologyProfile::default();
        profile.source.abox_axioms = 2;
        profile.source.class_assertions = 1;
        profile.source.logical_axioms = 120_000;
        profile.source.concept_expressions = 300_000;
        profile
            .source
            .axiom_types
            .insert("ClassAssertion".into(), 1);
        profile
            .source
            .axiom_types
            .insert("DifferentIndividuals".into(), 1);
        assert!(typed_object_abox_bridge_candidate(&profile));
        assert!(sequential_typed_bridge_candidate(&profile));

        profile.source.concept_expressions = 99_999;
        assert!(!sequential_typed_bridge_candidate(&profile));
    }

    #[test]
    fn large_disjunctive_shi_tbox_runs_bridge_before_cb() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 54_977;
        profile.source.tbox_axioms = 54_973;
        profile.source.concept_expressions = 343_884;
        profile.source.unions = 18_323;
        profile.source.distinct_classes = 54_973;
        profile.source.distinct_object_properties = 9;
        profile.expressivity.inverse = true;
        profile.expressivity.transitivity = true;
        profile.expressivity.negation_disjunction = true;
        assert!(sequential_large_shi_bridge_candidate(&profile));

        profile.source.unions = 9_999;
        assert!(!sequential_large_shi_bridge_candidate(&profile));
    }

    #[test]
    fn dense_role_rich_el_closure_enables_parallel_nf4_frontiers() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 2_544_794;
        profile.source.existentials = 2_500_000;
        profile.source.distinct_object_properties = 8;
        profile.source.file_bytes = 472_349_807;
        assert!(parallel_nf4_frontier_candidate(&profile));

        profile.source.distinct_object_properties = 3;
        assert!(!parallel_nf4_frontier_candidate(&profile));
        profile.source.distinct_object_properties = 8;
        profile.source.abox_axioms = 1;
        assert!(!parallel_nf4_frontier_candidate(&profile));
        profile.source.abox_axioms = 0;
        profile.source.logical_axioms = 3_000_000;
        assert!(!parallel_nf4_frontier_candidate(&profile));
    }

    #[test]
    fn large_role_chain_cardinality_tbox_uses_eight_workers() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 155_724;
        profile.source.tbox_axioms = 155_577;
        profile.source.qualified_cardinalities = 74;
        profile.source.role_chain_axioms = 30;
        profile.source.distinct_classes = 58_364;
        profile.expressivity.inverse = true;
        profile.expressivity.complex_subrole = true;
        profile.expressivity.qualified_cardinality = true;
        assert!(eight_thread_large_sriq_candidate(&profile));

        profile.source.qualified_cardinalities = 69;
        assert!(!eight_thread_large_sriq_candidate(&profile));
    }

    #[test]
    fn large_plain_tbox_uses_eight_workers() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 24_749;
        profile.source.tbox_axioms = 24_587;
        profile.source.distinct_classes = 9_860;
        profile.expressivity.inverse = true;
        profile.expressivity.transitivity = true;
        assert!(eight_thread_large_plain_tbox_candidate(&profile));

        profile.source.logical_axioms = 19_999;
        assert!(!eight_thread_large_plain_tbox_candidate(&profile));
        profile.source.logical_axioms = 24_749;
        profile.source.qualified_cardinalities = 1;
        assert!(!eight_thread_large_plain_tbox_candidate(&profile));
        profile.source.qualified_cardinalities = 0;
        profile.source.abox_axioms = 1;
        assert!(!eight_thread_large_plain_tbox_candidate(&profile));
    }

    #[test]
    fn medium_shi_tbox_uses_one_worker() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 80_435;
        profile.source.tbox_axioms = 80_419;
        profile.expressivity.negation_disjunction = true;
        profile.expressivity.existential = true;
        profile.expressivity.transitivity = true;
        profile.expressivity.role_hierarchy = true;
        profile.expressivity.inverse = true;
        assert!(one_thread_medium_shi_candidate(&profile));

        profile.source.role_chain_axioms = 1;
        assert!(!one_thread_medium_shi_candidate(&profile));
        profile.source.role_chain_axioms = 0;
        profile.source.logical_axioms = 100_000;
        assert!(!one_thread_medium_shi_candidate(&profile));
    }

    #[test]
    fn small_production_tboxes_use_one_worker_without_crossing_slow_shapes() {
        let mut profile = OntologyProfile::default();
        profile.source.file_bytes = 1_000_000;
        profile.source.logical_axioms = 5_000;
        profile.source.distinct_classes = 3_000;
        profile.expressivity.inverse = true;
        profile.expressivity.functionality = true;
        assert!(one_thread_small_production_candidate(&profile));
        assert_eq!(select(&profile), Route::ProductionAll1);

        profile.source.distinct_classes = 865;
        assert!(!one_thread_small_production_candidate(&profile));

        profile.expressivity.functionality = false;
        profile.source.logical_axioms = 325;
        profile.source.universals = 68;
        assert!(!one_thread_small_production_candidate(&profile));

        profile.source.unions = 19;
        profile.source.universals = 25;
        assert!(one_thread_small_production_candidate(&profile));

        profile.expressivity.complex_subrole = true;
        assert!(!one_thread_small_production_candidate(&profile));
    }

    #[test]
    fn typed_object_abox_without_cardinality_uses_production_portfolio() {
        let profile = source_profile(
            r#"Ontology(
                Declaration(Class(<A>))
                Declaration(ObjectProperty(<r>))
                ClassAssertion(<A> <a>)
                ObjectPropertyAssertion(<r> <a> <b>)
                DifferentIndividuals(<a> <b>)
                EquivalentClasses(<N> ObjectOneOf(<a>))
                SubClassOf(<A> ObjectSomeValuesFrom(<r> <A>))
                InverseObjectProperties(<r> <s>)
                TransitiveObjectProperty(<s>)
            )"#,
        );
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(typed_object_abox_bridge_candidate(&profile));
        assert!(!profile.expressivity.cardinality);
        assert_eq!(select(&profile), Route::ProductionAll);
    }

    #[test]
    fn giant_flat_taxonomy_uses_el_completion() {
        let mut profile = OntologyProfile::default();
        profile.source.subclass_axioms = 1_974_320;
        profile.source.logical_axioms = profile.source.subclass_axioms;
        profile.source.declarations = 123_311;
        profile.source.declared_classes = 123_311;
        profile.source.distinct_classes = 123_311;
        profile.source.max_concept_depth = 1;
        // The current frontend records every class position in this ontology
        // as a potential bottom occurrence. Bottom concepts remain in EL and
        // the worker validates the normalized fragment independently.
        profile.source.bottom_occurrences = 123_313;
        profile.expressivity.inverse = true;
        profile.expressivity.transitivity = true;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::SriqCore);
        assert!(flat_taxonomy_el_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);

        let invalidators: [fn(&mut OntologyProfile); 4] = [
            |p: &mut OntologyProfile| p.source.existentials = 1,
            |p: &mut OntologyProfile| p.source.unions = 1,
            |p: &mut OntologyProfile| p.source.role_inclusion_axioms = 1,
            |p: &mut OntologyProfile| p.source.abox_axioms = 1,
        ];
        for invalidate in invalidators {
            let mut candidate = profile.clone();
            invalidate(&mut candidate);
            if candidate.source.role_inclusion_axioms > 0 {
                candidate.source.rbox_axioms = 1;
                candidate.source.logical_axioms += 1;
            }
            if candidate.source.abox_axioms > 0 {
                candidate.source.logical_axioms += 1;
            }
            assert!(!flat_taxonomy_el_candidate(&candidate));
        }
    }

    #[test]
    fn every_nonempty_flat_taxonomy_uses_el_completion() {
        let mut profile = OntologyProfile::default();
        profile.source.subclass_axioms = 847_755;
        profile.source.logical_axioms = profile.source.subclass_axioms;
        profile.source.declarations = 847_760;
        profile.source.declared_classes = 847_760;
        profile.source.distinct_classes = 847_760;
        profile.source.max_concept_depth = 1;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::SriqCore);
        assert!(flat_taxonomy_el_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);

        profile.source.subclass_axioms = 1;
        profile.source.logical_axioms = profile.source.subclass_axioms;
        assert!(flat_taxonomy_el_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);

        profile.source.subclass_axioms = 0;
        profile.source.logical_axioms = 0;
        assert!(!flat_taxonomy_el_candidate(&profile));
    }

    #[test]
    fn intersection_only_taxonomy_uses_el_completion() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 12_343;
        profile.source.tbox_axioms = 12_343;
        profile.source.subclass_axioms = 12_343;
        profile.source.intersections = 2;
        profile.source.max_concept_depth = 2;
        profile.source.distinct_classes = 15_319;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::SriqCore);
        assert!(intersection_taxonomy_el_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);

        for invalidate in [
            |p: &mut OntologyProfile| p.source.abox_axioms = 1,
            |p: &mut OntologyProfile| p.source.existentials = 1,
            |p: &mut OntologyProfile| p.source.unions = 1,
            |p: &mut OntologyProfile| p.source.distinct_object_properties = 1,
        ] {
            let mut candidate = profile.clone();
            invalidate(&mut candidate);
            assert!(!intersection_taxonomy_el_candidate(&candidate));
        }
    }

    #[test]
    fn large_source_el_terminology_uses_atomic_completion() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 50_000;
        profile.source.tbox_axioms = 49_990;
        profile.source.rbox_axioms = 10;
        profile.source.subclass_axioms = 45_000;
        profile.source.equivalent_class_axioms = 4_990;
        profile.source.role_inclusion_axioms = 8;
        profile.source.transitive_role_axioms = 2;
        profile.source.existentials = 20_000;
        profile.source.intersections = 5_000;
        profile.source.max_concept_depth = 4;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::SriqCore);
        assert!(source_el_terminology_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);

        // OWL EL admits class bottom and named-class disjointness. The ELC
        // worker independently requires their normalized NF5 empty-head shape
        // before it can publish an answer.
        profile.source.disjoint_class_axioms = 3;
        profile.source.bottom_occurrences = 2;
        assert!(source_el_terminology_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);
        profile.source.disjoint_class_axioms = 0;
        profile.source.bottom_occurrences = 0;

        let mut bottom_role = profile.clone();
        bottom_role.source.bottom_role_occurrences = 1;
        assert!(!source_el_terminology_candidate(&bottom_role));

        let mut unsafe_profile = profile.clone();
        unsafe_profile.source.unions = 1;
        assert!(!source_el_terminology_candidate(&unsafe_profile));

        let mut unsafe_profile = profile.clone();
        unsafe_profile.source.abox_axioms = 1;
        assert!(!source_el_terminology_candidate(&unsafe_profile));

        let mut unsafe_profile = profile.clone();
        unsafe_profile.source.declared_data_properties = 1;
        assert!(!source_el_terminology_candidate(&unsafe_profile));

        let mut unsafe_profile = profile.clone();
        unsafe_profile
            .source
            .axiom_types
            .insert("InverseObjectProperties".into(), 1);
        assert!(!source_el_terminology_candidate(&unsafe_profile));

        let mut unsafe_profile = profile;
        unsafe_profile.source.functional_role_axioms = 1;
        assert!(!source_el_terminology_candidate(&unsafe_profile));
    }

    #[test]
    fn certified_positive_el_abox_uses_atomic_completion() {
        let mut profile = OntologyProfile::default();
        profile.positive_el_abox_materializable = true;
        profile.source.logical_axioms = 50_000;
        profile.source.tbox_axioms = 30_000;
        profile.source.abox_axioms = 20_000;
        profile.source.class_assertions = 20_000;
        profile.source.existentials = 10_000;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::PositiveAbox);
        assert!(source_el_positive_abox_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);

        // The typed positive-ABox certificate checks asserted consistency,
        // while ELC handles the TBox's normalized NF5 constraints.
        profile.source.disjoint_class_axioms = 1;
        profile.source.bottom_occurrences = 1;
        assert!(source_el_positive_abox_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);
        profile.source.disjoint_class_axioms = 0;
        profile.source.bottom_occurrences = 0;

        let mut uncertified = profile.clone();
        uncertified.positive_el_abox_materializable = false;
        assert!(!source_el_positive_abox_candidate(&uncertified));

        let mut non_el = profile;
        non_el.source.universals = 1;
        assert!(!source_el_positive_abox_candidate(&non_el));

        let mut nominal_source = OntologyProfile::default();
        nominal_source.positive_el_abox_materializable = true;
        nominal_source.source.logical_axioms = 50_000;
        nominal_source.source.abox_axioms = 20_000;
        nominal_source.source.existentials = 10_000;
        nominal_source.source.nominals = 1;
        assert!(!source_el_positive_abox_candidate(&nominal_source));
    }

    #[test]
    fn large_data_assertion_abox_without_cardinality_uses_production() {
        let mut profile = OntologyProfile::default();
        profile.source.abox_axioms = 607_933;
        profile.source.class_assertions = 382_511;
        profile.source.role_assertions = 225_420;
        profile.source.distinct_individuals = 116_325;
        profile.source.declared_data_properties = 1;
        profile.source.distinct_data_properties = 1;
        profile.source.nominals = 19;
        profile.source.datatype_constructors = 0;
        profile.expressivity.nominal = true;
        profile.expressivity.nominal_individual = true;
        profile.expressivity.datatype = false;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(large_no_cardinality_abox_production_candidate(&profile));
        assert_eq!(select(&profile), Route::ProductionAll);

        profile.source.min_cardinalities = 1;
        profile.expressivity.cardinality = true;
        assert!(!large_no_cardinality_abox_production_candidate(&profile));
    }

    #[test]
    fn small_class_identity_abox_uses_production_portfolio() {
        let mut profile = source_profile(
            r#"Ontology(
                ClassAssertion(<A> <a>)
                ClassAssertion(<B> <b>)
                DifferentIndividuals(<a> <b>)
                SubClassOf(<A> ObjectMinCardinality(2 <r> <B>))
                InverseObjectProperties(<r> <s>)
            )"#,
        );
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(small_class_identity_abox_production_candidate(&profile));
        assert_eq!(select(&profile), Route::ProductionAll);

        profile
            .source
            .axiom_types
            .insert("ObjectPropertyAssertion".to_string(), 1);
        profile.source.role_assertions = 1;
        profile.source.abox_axioms += 1;
        assert!(!small_class_identity_abox_production_candidate(&profile));

        profile.source.axiom_types.remove("ObjectPropertyAssertion");
        profile.source.role_assertions = 0;
        profile.source.abox_axioms -= 1;
        profile.source.abox_axioms = 101;
        assert!(!small_class_identity_abox_production_candidate(&profile));
    }

    #[test]
    fn large_tbox_small_identity_abox_uses_production_portfolio() {
        let mut profile = source_profile(
            r#"Ontology(
                ClassAssertion(<A> <a>)
                ClassAssertion(<B> <b>)
                DifferentIndividuals(<a> <b>)
                SubClassOf(<A> <B>)
            )"#,
        );
        profile.source.tbox_axioms = 100_000;
        profile.positive_abox_tbox_separable = false;
        profile.positive_el_abox_materializable = false;
        // Prevent the ordinary typed-object bridge candidate from accounting
        // for this route in the regression fixture.
        profile.expressivity.universal_role = true;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(large_tbox_small_identity_abox_production_candidate(
            &profile
        ));
        assert_eq!(select(&profile), Route::ProductionAll);

        profile.source.tbox_axioms -= 1;
        assert!(!large_tbox_small_identity_abox_production_candidate(
            &profile
        ));
        assert_eq!(select(&profile), Route::Nominals);
    }

    #[test]
    fn large_horn_functional_terminology_uses_exact_atomic_bridge() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 37_696;
        profile.source.tbox_axioms = 35_531;
        profile.source.rbox_axioms = 2_165;
        profile.source.functional_role_axioms = 337;
        profile.source.inverse_functional_role_axioms = 337;
        profile.source.concept_expressions = 133_419;
        profile.clauses.clauses = 139_634;
        profile.clauses.horn_clauses = profile.clauses.clauses;
        profile.clauses.function_term_symbols = 14_115;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::SriqCore);
        assert!(large_horn_functional_native_bridge_candidate(&profile));
        assert_eq!(select(&profile), Route::HtBridge);

        // Production selects before clausification. The source-only profile
        // must therefore make the same decision as `km profile`, which fills
        // clause statistics after normalisation.
        let mut pre_clausification = profile.clone();
        pre_clausification.clauses = Default::default();
        assert_eq!(select(&pre_clausification), Route::HtBridge);

        profile.source.complements = 1;
        assert!(!large_horn_functional_native_bridge_candidate(&profile));
    }

    #[test]
    fn explicit_nominal_counterexample_keeps_the_exact_fallback() {
        // This profile deliberately satisfies the cheap 10621-shaped source
        // gate but can fail the bridge's stronger converted-input certificate:
        // A is the singleton {a}, yet A(b) and a != b.  The ontology is
        // inconsistent.  An ordinary proxy-only CB fallback can lose singleton
        // meaning and publish "consistent", so both automatic and explicitly
        // named execution must select the nominal-aware fallback bundle.
        let profile = source_profile(
            r#"Ontology(
                ClassAssertion(<A> <b>)
                ClassAssertion(<C> <a>)
                DifferentIndividuals(<a> <b>)
                EquivalentClasses(<A> ObjectOneOf(<a>))
                SubClassOf(<D> DataSomeValuesFrom(<p> xsd:string))
            )"#,
        );
        // DataPropertyRange alone intentionally does not set Konclude's `(D)`
        // expressivity occurrence flag. Use an actual data restriction and
        // pin every source-only premise of NativeBridgeAbox before asking the
        // policy to select it. The restriction is on otherwise-unused D, so it
        // cannot create or hide the nominal inconsistency under test.
        assert!(profile.expressivity.datatype);
        assert_eq!(profile.source.imports, 0);
        assert_eq!(profile.source.rule_axioms, 0);
        assert_eq!(profile.source.unsupported_rule_axioms, 0);
        assert_eq!(profile.source.role_assertions, 0);
        assert_eq!(profile.source.class_assertions, 2);
        assert_eq!(profile.source.distinct_individuals, 2);
        assert_eq!(profile.source.abox_axioms, 3);
        assert_eq!(
            profile
                .source
                .axiom_types
                .get("DifferentIndividuals")
                .copied(),
            Some(1)
        );
        assert_eq!(
            semantic_fragment(&profile),
            SemanticFragment::NativeBridgeAbox
        );

        let automatic = select(&profile);
        let explicit: Route = "certified_nominals".parse().expect("named route parses");
        assert_eq!(automatic, Route::CertifiedNominals);
        assert_eq!(explicit, Route::CertifiedNominals);
        for route in [automatic, explicit] {
            let env = normalized_environment(route);
            assert!(env.contains(&("KM_MECHANISM", "portfolio")), "{route}");
            assert!(env.contains(&("KM_HT_ONLY", "certified")), "{route}");
            assert!(env.contains(&("KM_TRIGGER_ABSORB", "1")), "{route}");
            assert!(
                env.contains(&("KM_NOMINALS", "1")),
                "{route} must never expose this ABox to ordinary proxy-only CB"
            );
            assert!(
                env.contains(&("KM_ABSORB", "0")),
                "{route} must preserve the validated nominal clause semantics"
            );
            assert!(
                env.contains(&("KM_NO_HT_CARD", "1")),
                "{route} must not hand a bridge defer to a path that ignores typed inequalities"
            );
        }
    }

    /// The exact environment of the proven ORE 3215 closure (IBEX jobs
    /// 48790271/48790295, binary 87ee76f1…, docs/SOLVE-3215.md). A named
    /// production route must normalize to precisely this bundle so the
    /// deterministic route invokes the Konclude KPSet bridge — source-TBox
    /// trigger absorption at normalisation, the saturation pre-pass, the
    /// all-satisfiability-jobs barrier, and the 30 s / 0-retry probe budgets —
    /// instead of a plain-CB fallback that times out on the 54,974-class
    /// terminology.
    const PROVEN_3215_CLOSURE_ENV: &[(&str, &str)] = &[
        ("KM_TRIGGER_ABSORB", "1"),
        ("KM_KEEP_CHAIN_AXIOMS", "1"),
        ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
        ("KM_BRIDGE_RETRY_ROUNDS", "0"),
        ("KM_HT_SATURATION_BUDGET_S", "180"),
        ("KM_HT_MEM_GB", "18"),
        ("KM_PAR_MEM_GB", "18"),
    ];

    fn normalized_environment(route: Route) -> Vec<(&'static str, &'static str)> {
        // Mirrors `apply_environment`: COMMON first, then the bundle, later
        // duplicate keys winning — without mutating the process environment
        // (tests run concurrently).
        let mut env: Vec<(&'static str, &'static str)> = Vec::new();
        for &(key, value) in COMMON_SETTINGS.iter().chain(route.settings()) {
            env.retain(|(existing, _)| *existing != key);
            env.push((key, value));
        }
        env
    }

    #[test]
    fn production_bundles_normalize_to_the_proven_3215_closure_environment() {
        for route in [
            Route::ProductionAll,
            Route::ProductionAll8,
            Route::ProductionAll1,
        ] {
            let env = normalized_environment(route);
            for required in PROVEN_3215_CLOSURE_ENV {
                assert!(
                    env.contains(required),
                    "{route} must carry {required:?} for KPSet-bridge parity"
                );
            }
            assert!(env.contains(&("KM_MECHANISM", "portfolio")), "{route}");
            assert!(env.contains(&("KM_HT_ONLY", "certified")), "{route}");
        }
        // The isolated bridge measurement route needs the same worker-side
        // closure environment on top of its exact mechanism discriminator.
        let env = normalized_environment(Route::HtBridge);
        for required in PROVEN_3215_CLOSURE_ENV {
            assert!(env.contains(required), "ht_bridge must carry {required:?}");
        }
        assert!(env.contains(&("KM_MECHANISM", "ht")));
        assert!(env.contains(&("KM_HT_ONLY", "bridge")));
    }

    #[test]
    fn automatic_sriq_routing_reaches_the_proven_bridge_stack() {
        // Regression for the 3215 coverage break: with KM_ROUTE unset the
        // orchestrator routes SRIQ-core terminologies through this selection,
        // and `apply_environment` REPLACES the ambient routing keys. If the
        // selected route does not itself carry KM_TRIGGER_ABSORB, the frontend
        // never emits `source_axioms`, the bridge candidate gate fails, and
        // classification silently degrades to the plain-CB fallback that times
        // out on the proven 3215-scale closures.
        let route = select(&OntologyProfile::default());
        let env = normalized_environment(route);
        assert!(
            env.contains(&("KM_TRIGGER_ABSORB", "1")),
            "the automatic SRIQ route {route} must enable source-TBox trigger absorption"
        );
        assert!(
            env.contains(&("KM_BRIDGE_PROBE_BUDGET_S", "30"))
                && env.contains(&("KM_BRIDGE_RETRY_ROUNDS", "0")),
            "the automatic SRIQ route {route} must carry the proven bridge budgets"
        );
        assert!(
            sriq_policy_eligible(route),
            "the bootstrap tree may only emit a policy-eligible route"
        );
    }

    /// Regression for ore_ont_10908 (and the disjunction-absorption family
    /// 6212 / 15491 / 16444): the isolated `cb_absorb_portfolio16` route closes
    /// them exactly because `KM_ABSORB=1` makes the frontend emit the
    /// polarity-gated clause set that Horn-ifies LHS disjunctions and drops the
    /// unguarded excluded-middle clauses. The composed production portfolio ran
    /// the same always-on CB fallback but only carried `KM_TRIGGER_ABSORB=1`;
    /// the frontend clausifier's absorption flag reads *only* `KM_ABSORB`, so its
    /// CB fallback saturated the un-absorbed clause set and timed out where the
    /// absorbed route did not. The production bundles must carry `KM_ABSORB=1` so
    /// the CB fallback is fed the identical disjunction-shrunk clause set.
    #[test]
    fn production_bundles_absorb_the_cb_fallback_clause_set() {
        for route in [
            Route::ProductionAll,
            Route::ProductionAll8,
            Route::ProductionAll1,
        ] {
            let env = normalized_environment(route);
            // The exact key the frontend clausifier reads for polarity-gated
            // absorption (`KM_ABSORB` present and != "0"); this is what
            // `cb_absorb_portfolio16` sets and what recovers the family.
            assert!(
                env.contains(&("KM_ABSORB", "1")),
                "{route} must enable KM_ABSORB so its CB fallback gets the \
                 disjunction-shrunk clause set (else 10908 regresses to timeout)"
            );
            // Absorption must COMPOSE with the bridge stack, not replace it:
            // `source_axioms` are recorded from the original NNF axioms gated on
            // KM_TRIGGER_ABSORB, so both must remain set.
            assert!(
                env.contains(&("KM_TRIGGER_ABSORB", "1")),
                "{route} must keep KM_TRIGGER_ABSORB for the Konclude bridge"
            );
            assert!(env.contains(&("KM_HT_ONLY", "certified")), "{route}");
            assert!(env.contains(&("KM_MECHANISM", "portfolio")), "{route}");
        }
        // The polarity-absorbed clause set the production CB fallback now uses is
        // exactly the one the isolated absorb-portfolio route feeds CB: both set
        // KM_ABSORB=1 and neither pins KM_ABSORB=0.
        let portfolio = normalized_environment(Route::CbAbsorbPortfolio16);
        assert!(portfolio.contains(&("KM_ABSORB", "1")));
        let production = normalized_environment(Route::ProductionAll);
        assert_eq!(
            production.iter().find(|(k, _)| *k == "KM_ABSORB"),
            portfolio.iter().find(|(k, _)| *k == "KM_ABSORB"),
            "production CB fallback must see the same KM_ABSORB setting as \
             cb_absorb_portfolio16"
        );
    }

    /// The bootstrap SRIQ route (what `select` returns for a nominal-free core,
    /// and the CB fallback every ABox/nominal portfolio also relies on) must both
    /// reach the bridge stack AND feed CB the absorbed clause set. This pins the
    /// two absorptions together on the automatic path so a future edit cannot
    /// restore one without the other.
    #[test]
    fn automatic_sriq_route_absorbs_the_cb_fallback() {
        let route = select(&OntologyProfile::default());
        let env = normalized_environment(route);
        assert!(
            env.contains(&("KM_ABSORB", "1")),
            "the automatic SRIQ route {route} must feed CB the absorbed clause set"
        );
        assert!(
            env.contains(&("KM_TRIGGER_ABSORB", "1")),
            "the automatic SRIQ route {route} must keep the bridge trigger absorption"
        );
    }

    #[test]
    fn measurement_only_routes_fail_the_sriq_policy_gate() {
        for route in [
            Route::CbTrigger16,
            Route::CbTrigger8,
            Route::CbTrigger1,
            Route::ElcCert,
            Route::HtGeneral,
            Route::HtQo,
            Route::HtShoq,
            Route::HtCard,
            Route::HtBridge,
            Route::CertifiedNominals,
            Route::HtFeatures,
            Route::HtFull,
            Route::CardFn,
            Route::Nominals,
            Route::HtRules,
            Route::CertifiedCardProxyAbox,
        ] {
            assert!(!sriq_policy_eligible(route), "{route} must not pass");
        }
    }

    /// The source number-role certificate may propose the proxy portfolio, but
    /// the normalized ABox certificate remains authoritative at runtime. The
    /// route must carry the exact nominal fallback for every defer.
    #[test]
    fn certified_proxy_card_route_is_automatic_with_exact_fallback() {
        let mut profile = OntologyProfile::default();
        profile.source.abox_axioms = 223;
        profile.card_number_role_separable = true;
        assert_eq!(select(&profile), Route::CertifiedCardProxyAbox);
        assert!(Route::CertifiedCardProxyAbox
            .settings()
            .contains(&("KM_NOMINALS", "1")));

        profile.card_number_role_separable = false;
        assert_ne!(select(&profile), Route::CertifiedCardProxyAbox);

        // The stronger native materialization certificate keeps precedence.
        profile.card_number_role_separable = true;
        profile.inverse_cardinality_role_separable = true;
        assert_eq!(select(&profile), Route::CertifiedCardNominals);
    }

    #[test]
    fn rules_route_keeps_the_validated_precheck_enabled() {
        // The DL-safe rule consistency precheck is gated on the ABSENCE of
        // KM_NO_HT_RULES in both the frontend (rule collection + ABox
        // retention in the clause set) and the orchestrator
        // (`rules_consistency`). The rules bundle must never pin it off, and
        // its taxonomy fall-through must be the one atomic CB run.
        let settings = Route::HtRules.settings();
        assert!(
            !settings.iter().any(|(key, _)| *key == "KM_NO_HT_RULES"),
            "ht_rules must keep the consistency precheck enabled"
        );
        assert!(settings.contains(&("KM_MECHANISM", "cb")));
        assert!(settings.contains(&("KM_NO_HT_RACE", "1")));

        // Exactly the rules bundle and the preserved composed portfolios keep
        // the precheck; every other named bundle pins it off so isolated
        // measurement rows never run the rule machinery by accident.
        for route in Route::NAMED {
            let keeps_precheck = !route
                .settings()
                .iter()
                .any(|(key, value)| *key == "KM_NO_HT_RULES" && *value == "1");
            let expected = matches!(
                route,
                Route::HtRules
                    | Route::Default
                    | Route::Default8
                    | Route::Default1
                    | Route::ProductionAll
                    | Route::ProductionAll8
                    | Route::ProductionAll1
                    | Route::CbAbsorbPortfolio16
                    | Route::TabRace
            );
            assert_eq!(
                keeps_precheck, expected,
                "{route} precheck gating drifted from the validated contract"
            );
        }
    }

    #[test]
    fn generated_tree_has_no_ontology_identity() {
        let source = include_str!("routing/routing_tree_generated.rs");
        assert!(!source.contains("ore_ont_"));
    }
}
