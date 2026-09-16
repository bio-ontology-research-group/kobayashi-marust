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
    /// Exact absorbed/plain CB portfolio without speculative EL, HT, or
    /// tableau arms and without trigger-absorption bridge preprocessing.
    CbPortfolio16,
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
    pub const NAMED: [Route; 40] = [
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
        Route::CbPortfolio16,
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
            Route::CbPortfolio16 => "cb_portfolio16",
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
            Route::CbPortfolio16 => CB_PORTFOLIO,
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
            "cb_portfolio16" | "cb_portfolio" => Route::CbPortfolio16,
            "elc" => Route::Elc,
            "elc_cert" => Route::ElcCert,
            "certified_el_production" | "elc_cert_production" => Route::CertifiedElProduction,
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

/// Bounded subject partition for the certified typed-nominal bridge.
///
/// The large 10621-shaped terminology has enough independent subject work to
/// benefit from eight workers. Smaller typed ABoxes retain four to avoid fixed
/// scheduling and memory overhead. This does not change the bridge certificate,
/// merge order, or exact nominal fallback.
pub(crate) fn certified_nominal_subject_workers(profile: &OntologyProfile) -> &'static str {
    if native_bridge_abox_eligible(profile)
        && profile.source.logical_axioms >= 100_000
        && profile.source.distinct_classes >= 40_000
    {
        "8"
    } else {
        "4"
    }
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
///
/// A universal role that occurs only as the super-role of tautological
/// `R ⊑ owl:topObjectProperty` inclusions is not an occurrence here: the
/// frontend removes those axioms and clears the profile flag before routing
/// (`frontend::top_role`), so such sources are ordinary typed-object
/// candidates and the bridge sees a role table without the builtin.
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

/// Compact expressive object-ABoxes for which the exact typed bridge should
/// run before the broader clause-level HT probe.  The bridge independently
/// validates converted-input coverage and the caller retains the unchanged
/// nominal-aware fallback after any defer, so this predicate affects only
/// attempt order.  Bounds avoid imposing a second frontend pass on large ABox
/// families where bridge construction cannot be a low-latency win.
pub(crate) fn compact_typed_bridge_first_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    typed_object_abox_bridge_candidate(profile)
        && source.logical_axioms <= 1_000
        && source.abox_axioms <= 500
        && source.distinct_classes <= 500
        && source.max_concept_depth >= 5
        && profile.clauses.clauses <= 3_000
        && profile.expressivity.inverse
        && profile.expressivity.transitivity
        && profile.expressivity.cardinality
        && profile.expressivity.nominal
}

/// Automatic nominal routes that replaced the historical TBox-only production
/// schedule because its CB fallback did not carry singleton/ABox semantics.
///
/// The orchestrator may still use that fast TBox schedule after the normalized
/// positive-ABox completion has independently certified consistency. A false
/// positive here costs one failed probe only: the normalized checker declines
/// before any TBox-only answer can be published, and classification resumes on
/// the exact nominal route. Source singleton/value concepts are excluded even
/// if their normalized projection looks EL: the positive-ABox checker rewrites
/// asserted individuals, but it does not certify `A ≡ {a}` identity semantics.
pub(crate) fn certified_nominal_production_probe_candidate(profile: &OntologyProfile) -> bool {
    profile.source.nominals == 0
        && profile.source.has_values == 0
        && (large_tbox_small_identity_abox_production_candidate(profile)
            || small_class_identity_abox_production_candidate(profile)
            || large_no_cardinality_abox_production_candidate(profile)
            || (typed_object_abox_bridge_candidate(profile)
                && !profile.expressivity.cardinality
                && !profile.expressivity.qualified_cardinality
                && !profile.expressivity.datatype))
}

/// Nominal source families for which the isolated general hypertableau is a
/// cheaper exact first attempt than root-context nominal materialization.
///
/// This predicate never authorizes publication by itself. The converted-input
/// HT worker must consume every normalized clause and return a complete answer;
/// any structural refusal restores the ordinary exact nominal route. The two
/// families are class/identity-only ABoxes over expressive qualified-number
/// TBoxes and very large number-free ABoxes carrying otherwise unconstrained
/// data assertions. Both make nominal CB expensive, while the complete general
/// conversion retains their ground semantics directly.
pub(crate) fn certified_nominal_general_ht_probe_candidate(profile: &OntologyProfile) -> bool {
    let count = |name: &str| profile.source.axiom_types.get(name).copied().unwrap_or(0);
    small_class_identity_abox_production_candidate(profile)
        || large_identity_nominal_abox_general_ht_candidate(profile)
        || (large_no_cardinality_abox_production_candidate(profile)
            && (count("DataPropertyAssertion") > 0 || count("NegativeDataPropertyAssertion") > 0))
        || (typed_object_abox_bridge_candidate(profile)
            && (profile.source.nominals > 0 || profile.source.has_values > 0))
        || compact_abox_general_ht_candidate(profile)
        || one_worker_source_nominal_free_ht_candidate(profile)
}

/// Small, flat, role-rich ABoxes for which complete clause-level HT avoids the
/// fixed cost of nominal root-context materialisation.
///
/// This predicate schedules only a probe. `ht_general` must consume the full
/// normalized ABox and terminology before it may publish; any unsupported
/// clause restores the exact nominal CB route. The measured ORE member has a
/// shallow domain/range terminology around a modest object-property graph.
pub(crate) fn compact_role_assertion_general_ht_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.logical_axioms <= 1_000
        && (100..=1_000).contains(&source.abox_axioms)
        && source.distinct_object_properties >= 32
        && source.role_assertions > 0
        && source.has_values > 0
        && source.max_concept_depth <= 1
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.datatype_constructors == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.role_chain_axioms == 0
        && source.has_self == 0
        && profile.clauses.clauses <= 2_000
}

/// Compact expressive object ABoxes whose complete general-HT probe has too
/// little independent classification work to amortize the default fan-out.
/// This changes worker scheduling only; the probe still validates lossless
/// normalized TBox and ABox coverage before publishing an answer.
pub(crate) fn four_worker_compact_expressive_ht_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    typed_object_abox_bridge_candidate(profile)
        && (300..=1_000).contains(&source.logical_axioms)
        && (50..=500).contains(&source.abox_axioms)
        && (100..=500).contains(&source.distinct_classes)
        && (32..=100).contains(&source.distinct_object_properties)
        && (2..=4).contains(&source.max_concept_depth)
        && profile.clauses.clauses <= 2_000
        && profile.expressivity.inverse
        && profile.expressivity.transitivity
        && profile.expressivity.cardinality
        && profile.expressivity.nominal
        && !profile.expressivity.qualified_cardinality
        && !profile.expressivity.datatype
        && !profile.expressivity.complex_subrole
        && !profile.expressivity.universal_role
}

/// Compact datatype/has-value ABoxes whose complete general-HT probe needs a
/// third worker to meet both the latency and allocator-arena RSS envelope.
/// The worker count changes only scheduling of independent classification
/// jobs; converted-input coverage and result publication remain unchanged.
pub(crate) fn three_worker_compact_datatype_ht_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    typed_object_abox_bridge_candidate(profile)
        && (100..=250).contains(&source.logical_axioms)
        && (1..=10).contains(&source.abox_axioms)
        && (64..=128).contains(&source.distinct_classes)
        && (16..=32).contains(&source.distinct_object_properties)
        && (1..=10).contains(&source.distinct_data_properties)
        && (2..=3).contains(&source.max_concept_depth)
        // Source routing runs before normalized clause statistics are
        // populated (`clauses == 0`). Retain only the post-normalization upper
        // fence so the same predicate is valid in both routing phases.
        && profile.clauses.clauses <= 600
        && source.has_values > 0
        && source.role_assertions > 0
        && profile.expressivity.datatype
        && profile.expressivity.inverse
        && profile.expressivity.transitivity
        && profile.expressivity.cardinality
        && !profile.expressivity.nominal
        && !profile.expressivity.qualified_cardinality
}

/// ABox layouts for which the complete clause-level hypertableau is much
/// smaller than eager nominal root-context materialisation.
///
/// This is only a scheduling predicate. `ht_general` independently checks that
/// it consumed the complete normalized input and otherwise defers to the exact
/// nominal fallback. The source/normalized bounds avoid imposing that probe on
/// the large, complement-heavy biomedical TBoxes where it is known to be a
/// poor first attempt.
fn compact_abox_general_ht_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let clauses = &profile.clauses;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);
    if source.abox_axioms < 500
        || clauses.clauses > 20_000
        || source.role_chain_axioms > 0
        || source.has_self > 0
        || profile.expressivity.universal_role
    {
        return false;
    }

    let compact_singletons = source.nominals > 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && count("SameIndividual") == 0
        && clauses.clauses <= 2_000;
    let moderate_tbox = source.tbox_axioms >= 1_000
        && source.distinct_classes <= 2_000
        && clauses.disjunctive_clauses <= 10
        && source.max_concept_depth >= 3;
    let assertion_dominated_flat = source.abox_axioms >= 200_000
        && source.tbox_axioms <= 100
        && source.max_concept_depth <= 1
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        // Identity-heavy ABoxes have their own measured, fail-closed gate.
        // Letting this broader shape bypass that threshold turns the probe on
        // after the identity certificate has deliberately declined it.
        && count("SameIndividual") == 0;
    let large_atomic_datatype_abox = source.abox_axioms >= 10_000
        && source.tbox_axioms <= 1_000
        && source.datatype_constructors >= 8;

    compact_singletons || moderate_tbox || assertion_dominated_flat || large_atomic_datatype_abox
}

/// Identity-heavy benchmark ABoxes whose complete direct-clause HT projection
/// is substantially smaller than nominal root-context materialization. This is
/// only a probe predicate: `ht_general` must consume every normalized clause
/// and produce a complete answer, otherwise the exact nominal route remains
/// authoritative.
fn large_identity_nominal_abox_general_ht_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);
    large_no_cardinality_abox_production_candidate(profile)
        && source.nominals > 0
        && source.has_values == 0
        && source.distinct_individuals >= 20_000
        && count("SameIndividual") >= 10_000
        && count("DataPropertyAssertion") == 0
        && count("NegativeDataPropertyAssertion") == 0
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

/// Compact role-rich inverse/transitive terminologies for which the exact HT
/// bridge reaches its fixpoint before the production portfolio has finished
/// constructing parallel CB state. The bridge remains complete-answer-or-
/// defer and automatic routing installs `ProductionAll` after any refusal, so
/// this predicate changes scheduling only.
fn compact_role_rich_ht_bridge_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let clauses = &profile.clauses;
    source.abox_axioms == 0
        && (300..=2_000).contains(&source.logical_axioms)
        && clauses.clauses <= 4_000
        && source.distinct_object_properties >= 64
        && source.universals >= 50
        && source.role_chain_axioms == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && profile.expressivity.inverse
        && profile.expressivity.transitivity
        && profile.expressivity.negation_disjunction
        && !profile.expressivity.nominal
        && !profile.expressivity.datatype
}

/// Additional compact normalized families where a complete HT bridge avoids
/// disproportionately expensive CB context construction. These are structural
/// scheduling gates over the full source/profile vocabulary; no ontology name
/// participates. The worker must still return a complete certified answer, and
/// automatic routing retains the production fallback after any defer.
fn compact_normalized_ht_bridge_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let clauses = &profile.clauses;
    if source.abox_axioms != 0 {
        return false;
    }

    let compact_qualified = source.qualified_cardinalities > 0
        && source.logical_axioms <= 200
        && (source.qualified_cardinalities >= 2 || source.distinct_classes >= 50);
    let narrow_existential_hierarchy = (1_500..=1_800).contains(&source.logical_axioms)
        && (600..=750).contains(&source.distinct_classes)
        && source.distinct_object_properties <= 10
        && source.existentials >= 900
        && source.unions > 0;
    let role_dense_existentials = (400..=500).contains(&source.logical_axioms)
        && (100..=150).contains(&source.distinct_classes)
        && source.distinct_object_properties >= 100
        && (50..=100).contains(&source.existentials);
    let broad_named_hierarchy = (3_300..=3_500).contains(&source.logical_axioms)
        && source.distinct_classes >= 2_000
        && source.distinct_object_properties <= 16
        && source.unions == 0
        && source.universals == 0;
    let compact_functional_universal = source.logical_axioms < 300
        && source.functional_role_axioms > 0
        && source.universals >= 90
        && source.unions >= 30
        && source.complements >= 10;
    let compact_horn_shi = (2_500..=3_000).contains(&source.logical_axioms)
        && source.distinct_classes >= 2_000
        && source.distinct_object_properties <= 32
        && source.intersections >= 150
        && source.existentials >= 150
        && source.max_concept_depth <= 3
        && clauses.disjunctive_clauses == 0
        && clauses.clauses <= 4_000
        && profile.expressivity.inverse
        && profile.expressivity.transitivity
        && !profile.expressivity.cardinality
        && !profile.expressivity.nominal
        && !profile.expressivity.datatype;
    let compact_role_schema_shif = (800..=1_100).contains(&source.logical_axioms)
        && source.distinct_classes <= 128
        && source.distinct_object_properties >= 200
        && source.domain_axioms >= 200
        && source.range_axioms >= 200
        && source.inverse_functional_role_axioms > 0
        && clauses.clauses <= 2_000
        && profile.expressivity.inverse
        && profile.expressivity.functionality
        && !profile.expressivity.nominal
        && !profile.expressivity.datatype;

    compact_qualified
        || narrow_existential_hierarchy
        || role_dense_existentials
        || broad_named_hierarchy
        || compact_functional_universal
        || compact_horn_shi
        || compact_role_schema_shif
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

/// Small nominal worker inputs where releasing the consumed frontend arena
/// closes the measured memory gap without increasing wall time. Other nominal
/// shapes keep the allocator default: the same trim points increased sampled
/// tree RSS on a smaller SHOIF(D) control.
pub(crate) fn small_nominal_heap_trim_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    profile.expressivity.code == "SHOI"
        && (1_500..3_000).contains(&source.logical_axioms)
        && (1_000..2_000).contains(&source.distinct_classes)
        && (100..200).contains(&source.distinct_object_properties)
        && (150..300).contains(&source.distinct_individuals)
        && (100..300).contains(&source.abox_axioms)
        && (100..250).contains(&source.nominals)
        && (300_000..600_000).contains(&source.file_bytes)
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && profile.expressivity.nominal
        && !profile.expressivity.cardinality
        && !profile.expressivity.datatype
}

/// Compact, assertion-bearing nominal inputs whose exact singleton-aware CB
/// classification cannot amortize the default sixteen worker arenas.
///
/// This predicate changes only the worker count of [`Route::Nominals`]. The
/// same nominal clauses, rules, ordering, and complete fixpoint are retained.
/// Bounds are the envelope of the repeated Gold-6248 panel; projection over
/// the retained ORE profiles admits four measured inputs and no controls.
pub(crate) fn one_thread_compact_nominal_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    (50_000..=170_000).contains(&source.file_bytes)
        && (300..=900).contains(&source.logical_axioms)
        && (100..=320).contains(&source.abox_axioms)
        && (2..=3).contains(&source.max_concept_depth)
        && (35..=300).contains(&source.distinct_classes)
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
}

/// Small source-nominal-free ABoxes for which complete general HT avoids the
/// fixed cost of exact nominal-aware CB saturation.
///
/// The surrounding dispatcher invokes this predicate only after automatic
/// routing selected an exact nominal route.  It schedules a one-worker
/// `ht_general` probe; converted-input coverage remains the publication gate,
/// and any refusal restores the unchanged exact nominal fallback.  The final
/// exclusion keeps the separately measured exact-CB worker envelope on that
/// route.  Projection over the retained ORE profiles admits four measured
/// inputs and no controls.
pub(crate) fn one_worker_source_nominal_free_ht_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    !one_thread_compact_nominal_candidate(profile)
        && (50_000..=170_000).contains(&source.file_bytes)
        && (300..=900).contains(&source.logical_axioms)
        && (100..=320).contains(&source.abox_axioms)
        && (2..=4).contains(&source.max_concept_depth)
        && (25..=400).contains(&source.distinct_classes)
        && source.nominals == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
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

/// Small Horn-like terminologies with a tiny class-only ABox for which the
/// exact absorbed/plain CB stack finishes before either speculative portfolio
/// arm can contribute.  Suppressing those arms changes scheduling only: both
/// CB variants still compute the established complete fixpoint, while avoiding
/// the process and allocator high-water mark of the EL/HT conductors.
///
/// The transitive-role and role-hierarchy fences distinguish this measured SHI
/// family from the much larger flat biomedical ABoxes that use dedicated EL
/// routes.  Source constructs excluded below are precisely those that could
/// make a certified specialist useful before CB completes.
pub(crate) fn small_horn_abox_plain_cb_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    profile.disjoint_union_abox_candidate
        && (1_000..=5_000).contains(&source.logical_axioms)
        && (1..=32).contains(&source.abox_axioms)
        && source.class_assertions == source.abox_axioms
        && source.role_assertions == 0
        && source.transitive_role_axioms > 0
        && source.role_inclusion_axioms > 0
        && source.unions == 0
        && source.complements == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.nominals == 0
        && source.has_values == 0
        && source.datatype_constructors == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.role_chain_axioms == 0
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

/// Bridge-first production scheduling retains the exact CB fallback without
/// allocating it concurrently with a bridge known to dominate this source
/// shape. `Some` is also the bounded subject-worker count for that first arm.
pub(crate) fn production_bridge_subject_workers(profile: &OntologyProfile) -> Option<&'static str> {
    if eight_thread_large_sriq_candidate(profile) {
        Some("4")
    } else if sequential_large_shi_bridge_candidate(profile)
        || large_horn_functional_native_bridge_candidate(profile)
    {
        Some("2")
    } else {
        None
    }
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
    nominal_ni_tbox_layout(profile)
        && profile.source.logical_axioms == 889
        && profile.source.tbox_axioms == 355
}

/// Wine-family layout fence used to keep nearby TBox edits away from the
/// broader typed-ABox NI route. The latter is independently certified on its
/// admitted corpus shapes, but it must not become the fallback for a modified
/// TBox-only specialist merely because exact source counters changed.
pub(crate) fn nominal_ni_tbox_near_family(profile: &OntologyProfile) -> bool {
    nominal_ni_tbox_layout(profile)
        && profile.source.logical_axioms >= 889
        && profile.source.tbox_axioms >= 355
        && profile.source.logical_axioms == profile.source.tbox_axioms.saturating_add(534)
}

fn nominal_ni_tbox_layout(profile: &OntologyProfile) -> bool {
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

/// Compact nominal ontologies for which the converted-input HT certificate is
/// much cheaper than materializing every individual in CB root contexts.
///
/// This source profile gate schedules only an attempt. `ht_general`
/// independently checks complete clause coverage and returns DEFER on any
/// unsupported construct; automatic dispatch then runs the unchanged exact
/// nominal fallback. The complement fence avoids a measured family in which
/// HT remains exact but is slower than production completion.
fn compact_nominal_general_ht_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.abox_axioms > 0
        && source.role_assertions > 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && (6_000..=8_000).contains(&source.logical_axioms)
        && (1_500..=2_500).contains(&source.abox_axioms)
        && source.complements == 0
        && source.unions <= 2
        && (source.unions > 0 || source.role_assertions >= 400)
}

/// Large SRIQ terminology with a small positive ABox for which the general HT
/// conversion is complete and avoids the more expensive cardinality-proxy
/// portfolio. The source gate only schedules the certified attempt; a
/// converted-input refusal restores the exact nominal fallback.
fn large_card_general_ht_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    profile.card_number_role_separable
        && source.logical_axioms >= 10_000
        && source.abox_axioms > 0
        && source.abox_axioms <= 500
        && source.unions >= 100
        && source.qualified_cardinalities > 0
        && source.role_chain_axioms > 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
}

/// Small SHO(I)N ontologies whose standard clausal number encoding is much
/// larger than the source ontology.
///
/// The SHOQ worker is a complete procedure for this source fragment and
/// consumes the unqualified number restriction through its native path.  Keep
/// the gate at the source boundary: the motivating ORE family has one exact
/// cardinality of 300, for which general clausification creates tens of
/// thousands of equality clauses before classification starts.  Qualified
/// numbers, chains, self, data, rules, imports, and the universal role stay on
/// their existing complete routes.
pub(crate) fn high_unqualified_cardinality_shoq_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    source.max_cardinality >= 128
        && source.exact_cardinalities > 0
        && source.unqualified_cardinalities > 0
        && source.qualified_cardinalities == 0
        && source.role_chain_axioms == 0
        && source.has_self == 0
        && source.datatype_constructors == 0
        && source.distinct_data_properties == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && !profile.expressivity.qualified_cardinality
        && !profile.expressivity.datatype
        && !profile.expressivity.complex_subrole
        && !profile.expressivity.universal_role
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
        && source.abox_axioms
            == source
                .class_assertions
                .saturating_add(source.role_assertions)
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
        // Symmetry normalizes to the paired role inclusions already accepted
        // by the EL worker. The worker independently validates that normalized
        // clause/RBox shape and defers to production on any non-EL residue.
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

/// Inverse/chain EL-shaped terminologies accepted by the complete native
/// completion bridge.
///
/// Source inverse declarations and role domains/ranges keep this family out of
/// the atomic ELC gate, while the production portfolio needlessly allocates a
/// large CB competitor. The bridge independently checks lossless source,
/// clause, and RBox coverage and returns a complete answer or DEFER. Automatic
/// dispatch installs the unchanged production/nominal fallback after a defer,
/// so this source predicate changes scheduling only. It covers both the pure
/// terminology and the independently separable class-assertion ABox variant.
fn inverse_chain_el_bridge_candidate(profile: &OntologyProfile) -> bool {
    let source = &profile.source;
    let no_abox = source.abox_axioms == 0;
    let separable_class_abox = independent_large_abox_candidate(profile);

    (no_abox || separable_class_abox)
        && source.logical_axioms >= 10_000
        && source.logical_axioms <= 70_000
        && source.tbox_axioms >= 10_000
        && (8_000..=8_100).contains(&source.distinct_classes)
        && source.disjoint_class_axioms == 65
        && source.existentials >= 5_000
        && source.role_chain_axioms > 0
        && source.role_chain_axioms <= 12
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && source.unions == 0
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
        && profile.expressivity.inverse
        && profile.expressivity.complex_subrole
        && !profile.expressivity.cardinality
        && !profile.expressivity.qualified_cardinality
        && !profile.expressivity.nominal
        && !profile.expressivity.datatype
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

/// Bounded near-EL source screen for the certified EL completion.
///
/// [`certified_el_production_candidate`] only recognizes the very large
/// near-EL shapes (100k/400k source axioms). Below those floors the automatic
/// router hands every remaining nominal-free terminology to the absorbed
/// production portfolio, even when the source carries no construct outside the
/// EL class fragment and the only reason it misses [`source_el_shape`] is a
/// role-level feature (inverse/symmetric/transitive declarations, role
/// domains and ranges, data-property declarations) or the absence of an
/// existential restriction. Those inputs pay for the absorbed frontend plus a
/// CB classifier when plain normalization and the canonical-model certificate
/// decide them directly.
///
/// This predicate screens the source constructors only. It admits exactly the
/// EL class constructors (named subclass/equivalence, intersection,
/// existential restriction, named disjointness and class bottom, which `elc`
/// represents as NF5 empty-head clauses) and leaves every role-level feature
/// to the normalized certificate. Universal restriction, complement, number
/// restriction, nominal, `hasValue`, `hasSelf`, a bottom role, a negative
/// assertion, and the asymmetric/irreflexive constraints all fail closed here.
///
/// A source below 100 logical axioms keeps its established route: the absorbed
/// production frontend has nothing to save there, and the screen should not
/// perturb the clausification of trivial inputs.
///
/// Three bounds keep a refused attempt cheap, because the exact fallback runs
/// serially after it:
///
/// * `disjoint_class_axioms <= distinct_classes` rejects the near-complete
///   disjointness clique, whose pairwise bottom expansion is quadratic in the
///   class count and carries no positive EL structure to complete.
/// * `max_concept_depth <= 3` bounds the definer chains normalization
///   introduces, which is what the certificate has to discharge.
/// * `file_bytes <= 16 MiB` bounds the parse and normalization cost of an
///   attempt that the certificate then refuses.
///
/// Disjunction follows the bound the established certified-EL gates already
/// use, up to 100 unions that normalization absorbs, and only alongside a
/// genuine existential restriction and at most one union per hundred logical
/// axioms. A source whose only compound constructor is disjunction, or whose
/// disjunctions are a material part of the terminology, carries no EL
/// structure to complete, so the certificate can only refuse it.
///
/// The route this selects is [`Route::CertifiedElProduction`]: the normalized
/// EL worker publishes only on a passing canonical-model certificate, and any
/// refusal, residue, or worker failure reruns the established absorbed
/// production portfolio. The gate therefore changes scheduling only. Its
/// caller restricts it to the nominal-free `SriqCore`/`PositiveAbox`
/// fragments, where `production_all` is the exact automatic fallback and the
/// source is already ELC-publication-safe.
fn bounded_near_el_certified_candidate(profile: &OntologyProfile) -> bool {
    // Above this the refused attempt costs more than the scheduling win.
    // `certified_el_production_candidate` covers the large shapes it can
    // certify from the source alone.
    const REFUSAL_BUDGET_BYTES: u64 = 16 * 1024 * 1024;

    // The established certified-EL gates admit up to this many disjunctions
    // because normalization absorbs them; a source that carries nothing but
    // disjunction has no EL structure for the completion to work on.
    const ABSORBABLE_UNIONS: u64 = 100;
    // A disjunction is absorbable only relative to the terminology carrying
    // it. One union in four axioms is the terminology; one in twenty-six
    // thousand is a rounding error.
    const UNION_AXIOM_SHARE: u64 = 100;
    // Below this the absorbed production frontend has nothing to save, so the
    // established route keeps the trivial band and its clausification.
    const TRIVIAL_SOURCE_AXIOMS: u64 = 100;

    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);
    let el_shaped_disjunction = source.unions == 0
        || (source.existentials > 0
            && source.unions <= ABSORBABLE_UNIONS
            && source.unions.saturating_mul(UNION_AXIOM_SHARE) <= source.logical_axioms);

    source.logical_axioms >= TRIVIAL_SOURCE_AXIOMS
        && source.file_bytes <= REFUSAL_BUDGET_BYTES
        && source.max_concept_depth <= 3
        && source.disjoint_class_axioms <= source.distinct_classes
        && el_shaped_disjunction
        && source.complements == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.nominals == 0
        && source.has_values == 0
        && source.has_self == 0
        && source.bottom_role_occurrences == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && count("NegativeObjectPropertyAssertion") == 0
        && count("NegativeDataPropertyAssertion") == 0
        && count("AsymmetricObjectProperty") == 0
        && count("IrreflexiveObjectProperty") == 0
}

/// Worker count for the context-parallel EL completion, or `None` for the
/// established serial engine.
///
/// `elcomplete`'s context-parallel saturation owns context `c` on worker
/// `c % n`, exchanges every cross-context conclusion as a batched message, and
/// rebuilds each label from a sorted vector before it exits. It reaches the
/// same least fixpoint as the serial engine and writes byte-identical output
/// for every worker count, so this predicate is a scheduling choice only: it
/// changes no rule, no route, and no published answer. The worker itself is
/// the authority on whether the mode may run at all; it declines and stays
/// serial for the order-sensitive disciplines (`KM_ELC_PAR_NF4`,
/// `KM_ELC_FIFO`) and for every certificate mode, and it falls back to the
/// serial engine when a worker thread cannot start.
///
/// The measured basis is the paired IBEX panel of 2026-09-03 (array
/// `51251013`, Intel Xeon Gold 6248, 16 CPUs, three replicates of each of
/// four arms over the eighteen `elc`-routed strict residuals; 216 of 216 runs
/// returned `status=ok` with a gold-matching signature). Every one of the
/// eighteen improved its median wall at eight workers and none approached its
/// external peak target, while two workers were slower than the serial engine
/// on five of them. So the gate arms eight workers where the panel measured
/// eight, four where the machine cannot supply eight (four workers also
/// improved all eighteen), and declines below that rather than selecting the
/// two-worker arm the panel measured as a regression.
///
/// The source bounds admit the shape the panel covers and nothing else:
///
/// * `abox_axioms == 0` keeps the terminology-only family. The panel's two
///   ABox members hold its two largest peak increases (`ore_ont_6722` 314 ->
///   618 MiB, a factor of 1.97, and `ore_ont_1579` 819 -> 1101 MiB, 1.34,
///   against at most 302 -> 415 MiB and 1.38 for a terminology-only member),
///   and neither recovers a strict gate, so the individual layer stays on the
///   serial engine.
/// * The EL class fragment (no union, complement, universal restriction,
///   number restriction, nominal, `hasValue`, `hasSelf`, or datatype
///   constructor, `max_concept_depth <= 3`) is the fragment the panel
///   measured; anything else routed to `elc` reaches the completion through a
///   different normalization and carries no measurement here. Most of it is
///   already implied by the EL source certificate above; it is restated here
///   because it is this gate's own contract, not that gate's.
/// * The work floors (`100_000` logical axioms, `20_000` classes, `20_000`
///   existential restrictions) are the smallest panel member (`ore_ont_795`:
///   106,608 axioms, 47,144 classes, 24,595 existentials). Below them the
///   saturation lap is too small to repay eight thread starts and the message
///   buffers they allocate.
/// * The ceilings (`400_000` logical axioms, 64 MiB of source, 12 object
///   properties, 32 role chain axioms) and the eight-object-property floor
///   delimit the measured high-payoff family.  The complete 592-profile
///   projection admits nine sources, all present in the paired panel, while
///   excluding ten otherwise-matching sources for which no context-parallel
///   measurement exists.  They also keep the
///   ORE giants, whose completions run in gigabytes, on the serial engine,
///   where the 0-38% peak increase measured here has no evidence.
pub(crate) fn elc_context_parallel_workers(
    profile: &OntologyProfile,
    available: usize,
) -> Option<&'static str> {
    // The smallest measured member of the panel family.
    const MIN_LOGICAL_AXIOMS: u64 = 100_000;
    const MIN_CLASSES: u64 = 20_000;
    const MIN_EXISTENTIALS: u64 = 20_000;
    // Bounds that retain every measured strict recovery while admitting no
    // unmeasured member of the retained 592-profile corpus.
    const MAX_LOGICAL_AXIOMS: u64 = 400_000;
    const MAX_SOURCE_BYTES: u64 = 64 * 1024 * 1024;
    const MIN_OBJECT_PROPERTIES: u64 = 8;
    const MAX_OBJECT_PROPERTIES: u64 = 12;
    const MAX_ROLE_CHAIN_AXIOMS: u64 = 32;

    // The same source certificate the bare EL route selects on: no data
    // property, role domain or range, inverse declaration, or bottom role, and
    // an ABox-free terminology. Without it a profile of the right size can
    // carry source features the panel never measured, and the schedule would
    // be armed for a route that never runs the completion.
    if !source_el_terminology_candidate(profile) {
        return None;
    }

    let source = &profile.source;
    let el_class_fragment = source.unions == 0
        && source.complements == 0
        && source.universals == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.qualified_cardinalities == 0
        && source.nominals == 0
        && source.has_values == 0
        && source.has_self == 0
        && source.datatype_constructors == 0
        && source.max_concept_depth <= 3;
    let original_panel_family = (MIN_LOGICAL_AXIOMS..=MAX_LOGICAL_AXIOMS)
        .contains(&source.logical_axioms)
        && source.distinct_classes >= MIN_CLASSES
        && source.existentials >= MIN_EXISTENTIALS
        && source.file_bytes <= MAX_SOURCE_BYTES
        && (MIN_OBJECT_PROPERTIES..=MAX_OBJECT_PROPERTIES)
            .contains(&source.distinct_object_properties)
        && source.role_chain_axioms <= MAX_ROLE_CHAIN_AXIOMS;
    // A second measured terminology band has a wider role vocabulary but no
    // chains. Fifteen paired observations on the retained corpus member in
    // this band reduced median wall by 5.1% with unchanged peak and identical
    // output. Tight work/size intervals keep the 592-profile projection to
    // that measured family rather than widening the original role ceiling.
    let wide_role_chain_free_family = (150_000..=200_000).contains(&source.logical_axioms)
        && (60_000..=75_000).contains(&source.distinct_classes)
        && (90_000..=100_000).contains(&source.existentials)
        && source.file_bytes <= 40 * 1024 * 1024
        && (20..=32).contains(&source.distinct_object_properties)
        && source.role_chain_axioms == 0;
    let panel_family = source.abox_axioms == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && el_class_fragment
        && (original_panel_family || wide_role_chain_free_family);
    if !panel_family {
        return None;
    }
    match available {
        8.. => Some("8"),
        4..=7 => Some("4"),
        _ => None,
    }
}

/// Source-only screen for the certified positive-ABox Horn SHIF family that the
/// bare CB engine decides on its own.
///
/// These sources carry a large asserted graph (class assertions plus object
/// role assertions) over a small terminology whose class constructors are
/// intersection, existential and universal restriction only. Two consequences
/// follow from the source alone:
///
/// * The clause set is Horn. No source union, complement, named disjointness,
///   or number restriction can produce a disjunctive head, so the CB engine
///   never has to choose between incomparable disjunctive facts.
/// * At least one universal restriction occurs, so the source is outside the
///   EL class fragment and the portfolio's EL arm can only refuse.
///
/// The remaining portfolio arm is the certified Konclude bridge, whose probe
/// and conversion the CB engine has to be scheduled against. Over the fourteen
/// ORE members of this family the isolated CB bundle is faster on thirteen
/// (roughly twice as fast on the eight large members) and 2.7 ms slower on one,
/// and it lowers peak on thirteen (2026-07-27 route sweep,
/// `km_route_cb_absorb8` vs `km_route_production_all`).
///
/// The caller restricts this to `SemanticFragment::PositiveAbox`, so the source
/// certificate has already proved that the asserted graph is consistent and
/// cannot change any named-class subsumption. The CB engine classifies exactly
/// the retained terminology, which is what `production_all` would have made it
/// classify.
///
/// `file_bytes <= 128 MiB` bounds the attempt. Unlike the production portfolio,
/// an isolated CB bundle sets `KM_NO_RETRY=1`, so its RSS-capped attempt is not
/// repeated single-threaded; the bound keeps the screen inside the measured
/// envelope of this family, whose largest member is 63 MiB. A worker error or
/// RSS trip still returns to `production_all` through
/// [`automatic_atomic_fallback`].
fn positive_abox_horn_cb_candidate(profile: &OntologyProfile) -> bool {
    // Twice the largest measured member of this family.
    const ATTEMPT_BUDGET_BYTES: u64 = 128 * 1024 * 1024;

    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);

    source.abox_axioms > 0
        && source.class_assertions > 0
        && source.role_assertions > 0
        && source.file_bytes <= ATTEMPT_BUDGET_BYTES
        // Source-Horn: nothing here can clausify to a disjunctive head.
        && source.unions == 0
        && source.complements == 0
        && source.disjoint_class_axioms == 0
        && source.min_cardinalities == 0
        && source.max_cardinalities == 0
        && source.exact_cardinalities == 0
        && source.bottom_occurrences == 0
        // Outside the EL class fragment, so the EL arm of the portfolio can
        // only refuse, and genuinely existential, so this is not one of the
        // flat identity ABoxes the independent-ABox gates already recognize.
        && source.universals > 0
        && source.existentials > 0
        // Everything the positive-ABox screens leave to the exact nominal or
        // bridge routes fails closed here.
        && source.nominals == 0
        && source.has_values == 0
        && source.has_self == 0
        && source.bottom_role_occurrences == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && count("NegativeObjectPropertyAssertion") == 0
        && count("NegativeDataPropertyAssertion") == 0
        && count("SameIndividual") == 0
        && count("DifferentIndividuals") == 0
        && !profile.expressivity.nominal
        && !profile.expressivity.universal_role
}

/// Source-only screen for small nominal-free terminologies that no portfolio
/// arm other than CB can decide.
///
/// The screen requires a construct that is outside the EL class fragment in
/// every position: a universal restriction, a number restriction, or role
/// functionality. Any one of them forces the portfolio's EL arm to refuse
/// after paying for its own normalization, which leaves the CB engine to
/// decide the ontology while being scheduled against the certified bridge.
///
/// Two bounds keep the screen inside the family it was measured on:
///
/// * `logical_axioms <= 2_000` and `file_bytes <= 512 KiB`. The next larger
///   ORE terminologies this screen would otherwise admit are 11623 and 1016 at
///   4,529 and 5,771 source axioms, where every isolated CB arm is slower than
///   the portfolio, and then 7127, 7581, 9663, 9724 and 14817, where no
///   isolated CB arm in the 2026-07-27 sweep produces a result at all. An
///   isolated CB bundle has no portfolio arm left to answer instead.
/// * Disjunction density, using the bound the established certified-EL screens
///   already use: at most one union and at most one complement per hundred
///   logical axioms. The isolated CB bundles are precisely the arms that lose
///   to the portfolio on live disjunction, and this is what separates the
///   admitted sources from the disjunction-heavy small terminologies (ORE
///   11291, 12141, 4897, 5303 and 9024) whose CB arms are slower or do not
///   terminate at all.
///
/// A source below a hundred logical axioms keeps its established route: every
/// arm decides it in the same few tens of milliseconds, so there is nothing to
/// win and no reason to perturb it.
///
/// The caller restricts this to the nominal-free `SriqCore` fragment, where
/// `production_all` is the exact automatic fallback and remains reachable
/// through [`automatic_atomic_fallback`] after a worker error or RSS trip.
fn bounded_non_el_cb_terminology_candidate(profile: &OntologyProfile) -> bool {
    // Roughly twice the largest measured member; the next larger ORE
    // terminology of this shape is more than twice the bound and needs the
    // portfolio.
    const ATTEMPT_AXIOM_LIMIT: u64 = 2_000;
    const ATTEMPT_BUDGET_BYTES: u64 = 512 * 1024;
    // Below this every arm is equal and the established route stands.
    const TRIVIAL_SOURCE_AXIOMS: u64 = 100;
    // The established certified-EL bound: one disjunct per hundred axioms is a
    // rounding error, one in four is the terminology.
    const DISJUNCTION_AXIOM_SHARE: u64 = 100;

    let source = &profile.source;
    let count = |name: &str| source.axiom_types.get(name).copied().unwrap_or(0);
    let outside_el_class_fragment = source.universals > 0
        || source.min_cardinalities > 0
        || source.max_cardinalities > 0
        || source.exact_cardinalities > 0
        || source.functional_role_axioms > 0
        || source.inverse_functional_role_axioms > 0;

    source.abox_axioms == 0
        && outside_el_class_fragment
        && source.logical_axioms >= TRIVIAL_SOURCE_AXIOMS
        && source.logical_axioms <= ATTEMPT_AXIOM_LIMIT
        && source.file_bytes <= ATTEMPT_BUDGET_BYTES
        && source.unions.saturating_mul(DISJUNCTION_AXIOM_SHARE) <= source.logical_axioms
        && source.complements.saturating_mul(DISJUNCTION_AXIOM_SHARE) <= source.logical_axioms
        && source.nominals == 0
        && source.has_values == 0
        && source.bottom_role_occurrences == 0
        && source.imports == 0
        && source.rule_axioms == 0
        && source.unsupported_rule_axioms == 0
        && count("NegativeObjectPropertyAssertion") == 0
        && count("NegativeDataPropertyAssertion") == 0
        && !profile.expressivity.nominal
        && !profile.expressivity.universal_role
}

/// Isolated CB bundle for a source admitted by
/// [`bounded_non_el_cb_terminology_candidate`]. Every branch runs the same
/// complete CB mechanism on the same retained terminology; only clausification
/// and the worker count differ, so this choice cannot change the published
/// answer.
fn bounded_non_el_cb_terminology_route(profile: &OntologyProfile) -> Route {
    // Sixteen CB workers cannot amortize their per-worker arenas over fewer
    // than two class queries each.
    const SINGLE_WORKER_CLASS_LIMIT: u64 = 32;

    let source = &profile.source;
    if source.complements > 0 {
        // An explicit complement is what clausifies into the excluded-middle
        // clauses that polarity absorption (`KM_ABSORB`) shrinks, and this is
        // the clausification the production bundle already feeds its CB arm.
        Route::CbAbsorb8
    } else if source.distinct_classes <= SINGLE_WORKER_CLASS_LIMIT {
        // Neither absorption has anything to shrink, and the query set fits
        // one worker at the lowest peak.
        Route::CbPlain1
    } else {
        // Trigger absorption distributes the few union antecedents into clause
        // bodies, which is what the production bundle applies here too.
        Route::CbTrigger16
    }
}

/// Large ABoxes without number restrictions try the certified native bridge
/// before eagerly materializing every nominal in the CB root context. The
/// certified-nominals bundle retains the exact singleton-aware fallback even
/// when data-property assertions prevent a narrower bridge certificate.
fn large_no_cardinality_abox_production_candidate(profile: &OntologyProfile) -> bool {
    const LARGE_ABOX_AXIOMS: u64 = 40_000;
    let source = &profile.source;
    source.abox_axioms >= LARGE_ABOX_AXIOMS
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
/// They must use the exact nominal calculus: the ordinary production bundle
/// does not enable singleton-aware CB processing.
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

/// Very large terminologies with a tiny class/identity-only ABox try the typed
/// bridge before entering the nominal root-context engine. The
/// `certified_nominals` bundle retains that exact singleton-aware fallback.
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
pub(crate) fn large_horn_functional_native_bridge_candidate(profile: &OntologyProfile) -> bool {
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
    // The parsed frontend has replaced every individual's asserted named-type
    // conjunction by a fresh internal satisfiability probe and proved that
    // ground role edges and explicit inequalities are otherwise inert.
    if profile.inert_role_abox_probe_candidate {
        return Route::ProductionAll;
    }
    // The parsed frontend has proved that the ABox consists only of isolated
    // existential witnesses. ProductionAll classifies the projected TBox; the
    // orchestrator checks every recorded filler against its complete UNSAT set
    // before certifying full-ontology consistency.
    if profile.existential_witness_abox_candidate {
        return Route::ProductionAll;
    }
    if certified_el_production_candidate(profile) {
        return Route::CertifiedElProduction;
    }
    if inverse_chain_el_bridge_candidate(profile) {
        return Route::HtBridge;
    }
    if compact_role_rich_ht_bridge_candidate(profile)
        || compact_normalized_ht_bridge_candidate(profile)
    {
        return Route::HtBridge;
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
            Route::CertifiedNominals
        }
        SemanticFragment::Nominal if small_class_identity_abox_production_candidate(profile) => {
            Route::Nominals
        }
        SemanticFragment::Nominal if high_unqualified_cardinality_shoq_candidate(profile) => {
            Route::HtShoq
        }
        SemanticFragment::Nominal if compact_role_assertion_general_ht_candidate(profile) => {
            Route::HtGeneral
        }
        SemanticFragment::Nominal if compact_nominal_general_ht_candidate(profile) => {
            Route::HtGeneral
        }
        SemanticFragment::Nominal if large_card_general_ht_candidate(profile) => Route::HtGeneral,
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
        // Prefer the certified nominal portfolio for very large ABoxes when
        // no number restriction can couple their individuals.  This test must
        // precede the broad large-nominal portfolio: both routes retain the
        // exact nominal-aware CB fallback, but eagerly materializing this
        // shape can consume the whole process-tree budget before that fallback
        // gets useful work done.
        SemanticFragment::Nominal if large_no_cardinality_abox_production_candidate(profile) => {
            Route::CertifiedNominals
        }
        SemanticFragment::Nominal if large_nominal_portfolio_candidate(profile) => {
            Route::CertifiedNominals
        }
        // Typed object-ABoxes without number restrictions still require a
        // singleton-aware fallback if the bridge defers. CertifiedNominals
        // provides that exact fallback without admitting ordinary proxy CB.
        SemanticFragment::Nominal
            if typed_object_abox_bridge_candidate(profile)
                && !profile.expressivity.cardinality
                && !profile.expressivity.qualified_cardinality
                && !profile.expressivity.datatype =>
        {
            Route::CertifiedNominals
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
        // Run this large Horn SHIF shape bridge-first so its roughly 8-GiB arm
        // does not race the CB allocation. The bridge is complete-answer-or-
        // defer, not total: an honest converted-input decline must start the
        // exact production fallback instead of making automatic routing fail.
        SemanticFragment::SriqCore if large_horn_functional_native_bridge_candidate(profile) => {
            Route::ProductionAll
        }
        SemanticFragment::PositiveAbox if source_el_positive_abox_candidate(profile) => Route::Elc,
        SemanticFragment::PositiveAbox | SemanticFragment::SriqCore
            if profile.inverse_cardinality_role_separable =>
        {
            Route::ProductionAll
        }
        // A nominal-free source whose class constructors stay inside EL and
        // whose size bounds a refused attempt. The canonical-model certificate
        // decides whether the EL answer may be published; a refusal reruns the
        // exact absorbed production portfolio this arm would otherwise have
        // selected, so the source screen changes scheduling only. The
        // established one-worker production refinement below keeps priority:
        // it carries its own corpus measurement, and no ontology it recognizes
        // needs this schedule.
        SemanticFragment::PositiveAbox | SemanticFragment::SriqCore
            if bounded_near_el_certified_candidate(profile)
                && !one_thread_small_production_candidate(profile) =>
        {
            Route::CertifiedElProduction
        }
        // A certified positive ABox over a Horn, non-EL terminology. Both
        // remaining portfolio arms are inert here: the EL arm must refuse a
        // source carrying a universal restriction, and the certified bridge is
        // only ever scheduled against the CB engine that decides the ontology.
        // The isolated CB bundle consumes the same polarity-absorbed clause set
        // the production bundle feeds its CB arm, and `production_all` stays
        // the exact fallback after a worker error or RSS trip.
        SemanticFragment::PositiveAbox if positive_abox_horn_cb_candidate(profile) => {
            Route::CbAbsorb8
        }
        // A small nominal-free terminology outside the EL class fragment with
        // bounded disjunction. The same argument applies, and the bundle is
        // chosen from the source constructors that decide whether either
        // absorption or a sixteen-worker partition can pay for itself. The
        // established one-worker production refinement keeps priority.
        SemanticFragment::SriqCore
            if bounded_non_el_cb_terminology_candidate(profile)
                && !one_thread_small_production_candidate(profile) =>
        {
            bounded_non_el_cb_terminology_route(profile)
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

/// Exact fallback installed by the automatic supervisor after an atomic
/// complete-answer-or-defer specialist declines. Explicitly requested matrix
/// routes remain atomic. Nominal/ABox sources require the nominal-aware CB
/// calculus; nominal-free and certified-positive-ABox sources use the complete
/// production portfolio.
pub(crate) fn automatic_atomic_fallback(
    selected: Route,
    profile: &OntologyProfile,
) -> Option<Route> {
    let specialist = matches!(
        selected,
        Route::Elc
            | Route::HtGeneral
            | Route::HtBridge
            | Route::CertifiedCardNominals
            | Route::NominalNiTbox
            // The isolated CB bundles the source-feature screens select are
            // total procedures, not complete-answer-or-defer specialists, but
            // they drop the portfolio's single-threaded retry. A worker error,
            // a non-fixpoint exit, or an RSS trip must therefore return to the
            // exact route the screen displaced instead of failing the
            // classification.
            | Route::CbAbsorb8
            | Route::CbPlain1
            | Route::CbTrigger16
    );
    if !specialist {
        return None;
    }
    // The independently separable large-ABox routes classify a certified TBox
    // view and check every asserted class against its unsatisfiable set. Their
    // exact fallback is the production portfolio carrying that same
    // consistency certificate, not eager nominal root-context materialization.
    if independent_large_abox_candidate(profile) {
        return Some(Route::ProductionAll);
    }
    match semantic_fragment(profile) {
        SemanticFragment::NativeBridgeAbox | SemanticFragment::Nominal => Some(Route::Nominals),
        SemanticFragment::PositiveAbox | SemanticFragment::SriqCore => Some(Route::ProductionAll),
        SemanticFragment::Rules | SemanticFragment::UnsupportedRules => None,
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
            .chain(std::iter::once("KM_EL_ABOX_CHECK"))
            .chain(std::iter::once("KM_NO_SEPARABLE_ABOX_ELISION"))
            .chain(std::iter::once("KM_DISJOINT_UNION_ABOX_CONSISTENT"))
            .chain(std::iter::once("KM_DISJOINT_UNION_ABOX_DECLINED"))
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
const CB_PORTFOLIO: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_NO_ELC_PORTFOLIO", "1"),
    ("KM_NO_HT_RACE", "1"),
    ("KM_NO_HT_RULES", "1"),
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
    "KM_ELC_PAR_CTX",
    "KM_HEAP_TRIM",
    "KM_NO_HEAP_TRIM",
    "KM_NO_HT_RACE",
    "KM_NO_HT_QO_ROUTER",
    "KM_NO_HT_SHOQ",
    "KM_NO_HT_CARD",
    "KM_NATIVE_CARDINALITY_ONLY",
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
    "KM_HT_TOTAL_GLOBAL",
    "KM_HT_GLOBAL_NATIVE_ABOX",
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
    "KM_BRIDGE_SUBJECT_WORKERS",
    "KM_BRIDGE_NO_HIERARCHY_COUNTERMODELS",
    "KM_HT_COMPONENT_ABOX",
    "KM_SEQ_ORDER",
    "KM_NO_SEQ_ORDER",
];

#[cfg(test)]
mod tests {
    use super::*;

    fn wine_nominal_ni_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.expressivity.code = "SHOIN".into();
        profile.expressivity.nominal = true;
        profile.expressivity.inverse = true;
        profile.expressivity.cardinality = true;
        profile.expressivity.functionality = true;
        profile.expressivity.transitivity = true;
        profile.source.logical_axioms = 889;
        profile.source.tbox_axioms = 355;
        profile.source.rbox_axioms = 40;
        profile.source.abox_axioms = 494;
        profile.source.distinct_classes = 137;
        profile.source.distinct_object_properties = 16;
        profile.source.distinct_individuals = 206;
        profile.source.class_assertions = 227;
        profile.source.role_assertions = 247;
        profile.source.nominals = 74;
        profile.source.has_values = 174;
        profile.source.transitive_role_axioms = 1;
        profile.source.functional_role_axioms = 6;
        for (name, count) in [
            ("DataPropertyAssertion", 1),
            ("DataPropertyDomain", 1),
            ("DataPropertyRange", 1),
            ("DifferentIndividuals", 8),
            ("SameIndividual", 12),
        ] {
            profile.source.axiom_types.insert(name.into(), count);
        }
        profile
    }

    #[test]
    fn wine_tbox_extensions_stay_out_of_the_typed_abox_specialist() {
        let base = wine_nominal_ni_profile();
        assert!(nominal_ni_tbox_candidate(&base));
        assert!(nominal_ni_tbox_near_family(&base));

        let mut extended = base.clone();
        extended.source.logical_axioms += 1;
        extended.source.tbox_axioms += 1;
        assert!(!nominal_ni_tbox_candidate(&extended));
        assert!(nominal_ni_tbox_near_family(&extended));

        let mut changed_abox = base;
        changed_abox.source.logical_axioms += 1;
        changed_abox.source.abox_axioms += 1;
        assert!(!nominal_ni_tbox_near_family(&changed_abox));
    }

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
        assert!(certified_el_production_candidate(&large_near_el_profile()));
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

    /// Existential SI terminology with named disjointness and one union: the
    /// broad source-EL screen rejects it for the union, the flat/intersection
    /// taxonomy screens for the existentials, and the large certified screen
    /// for its size.
    fn bounded_near_el_terminology_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.schema_version = 2;
        profile.source.file_bytes = 5_503_375;
        profile.source.logical_axioms = 26_455;
        profile.source.tbox_axioms = 26_449;
        profile.source.rbox_axioms = 6;
        profile.source.subclass_axioms = 21_391;
        profile.source.equivalent_class_axioms = 4_381;
        profile.source.disjoint_class_axioms = 677;
        profile.source.distinct_classes = 25_648;
        profile.source.distinct_object_properties = 8;
        profile.source.transitive_role_axioms = 6;
        profile.source.intersections = 4_380;
        profile.source.existentials = 5_209;
        profile.source.unions = 1;
        profile.source.concept_expressions = 60_000;
        profile.source.max_concept_depth = 3;
        profile.expressivity.negation_disjunction = true;
        profile.expressivity.existential = true;
        profile
    }

    /// Equivalence-only terminology: no existential at all, so the source-EL
    /// screen (which requires one) never fires and the router hands it to the
    /// absorbed production portfolio.
    fn equivalence_only_near_el_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.schema_version = 2;
        profile.source.file_bytes = 5_200_473;
        profile.source.logical_axioms = 20_963;
        profile.source.tbox_axioms = 20_963;
        profile.source.equivalent_class_axioms = 20_963;
        profile.source.distinct_classes = 39_430;
        profile.source.concept_expressions = 41_926;
        profile.source.max_concept_depth = 1;
        profile
    }

    /// Role domain/range schema with a separable positive class-assertion
    /// ABox. The source-EL screens reject domain/range axioms outright.
    fn domain_range_near_el_positive_abox_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.schema_version = 2;
        profile.positive_abox_tbox_separable = true;
        profile.source.file_bytes = 134_959;
        profile.source.logical_axioms = 767;
        profile.source.tbox_axioms = 99;
        profile.source.abox_axioms = 478;
        profile.source.rbox_axioms = 190;
        profile.source.subclass_axioms = 99;
        profile.source.range_axioms = 190;
        profile.source.class_assertions = 478;
        profile.source.distinct_individuals = 478;
        profile.source.distinct_classes = 98;
        profile.source.distinct_object_properties = 180;
        profile.source.concept_expressions = 866;
        profile.source.max_concept_depth = 1;
        profile
    }

    #[test]
    fn automatic_route_certifies_bounded_near_el_sources() {
        for profile in [
            bounded_near_el_terminology_profile(),
            equivalence_only_near_el_profile(),
            domain_range_near_el_positive_abox_profile(),
        ] {
            assert!(
                bounded_near_el_certified_candidate(&profile),
                "source screen must admit the bounded near-EL shape"
            );
            assert!(
                !certified_el_production_candidate(&profile),
                "the large certified screen must not already cover it"
            );
            assert_eq!(
                select(&profile),
                Route::CertifiedElProduction,
                "bounded near-EL sources must schedule the certificate before production"
            );
        }
        assert_eq!(
            semantic_fragment(&domain_range_near_el_positive_abox_profile()),
            SemanticFragment::PositiveAbox
        );
        assert_eq!(
            semantic_fragment(&bounded_near_el_terminology_profile()),
            SemanticFragment::SriqCore
        );
    }

    #[test]
    fn bounded_near_el_route_keeps_the_certificate_and_exact_fallback() {
        // The route publishes only on a passing canonical-model certificate
        // (`KM_ELC_CERT`), and it is deliberately not atomic: the orchestrator
        // reruns the absorbed production portfolio on any refusal.
        let settings = Route::CertifiedElProduction.settings();
        assert!(settings.iter().any(|(key, _)| *key == "KM_ELC_CERT"));
        assert!(settings.iter().any(|(key, _)| *key == "KM_ELC_FORCE"));
        assert!(!Route::CertifiedElProduction.is_atomic());
    }

    #[test]
    fn bounded_near_el_gate_fails_closed_outside_the_el_class_fragment() {
        // Every construct outside the admitted EL class fragment must fall
        // back to the unchanged production route.
        let cases: [(&str, fn(&mut OntologyProfile)); 12] = [
            ("universal", |p| p.source.universals = 1),
            ("complement", |p| p.source.complements = 1),
            ("min cardinality", |p| p.source.min_cardinalities = 1),
            ("max cardinality", |p| p.source.max_cardinalities = 1),
            ("exact cardinality", |p| p.source.exact_cardinalities = 1),
            ("nominal", |p| p.source.nominals = 1),
            ("hasValue", |p| p.source.has_values = 1),
            ("hasSelf", |p| p.source.has_self = 1),
            ("bottom role", |p| p.source.bottom_role_occurrences = 1),
            ("import", |p| p.source.imports = 1),
            ("rule", |p| p.source.rule_axioms = 1),
            ("unsupported rule", |p| p.source.unsupported_rule_axioms = 1),
        ];
        for (label, mutate) in cases {
            let mut profile = bounded_near_el_terminology_profile();
            mutate(&mut profile);
            assert!(
                !bounded_near_el_certified_candidate(&profile),
                "{label} must fail the bounded near-EL screen closed"
            );
            assert_ne!(
                select(&profile),
                Route::CertifiedElProduction,
                "{label} must not reach the certified EL route"
            );
        }

        for name in [
            "NegativeObjectPropertyAssertion",
            "NegativeDataPropertyAssertion",
            "AsymmetricObjectProperty",
            "IrreflexiveObjectProperty",
        ] {
            let mut profile = bounded_near_el_terminology_profile();
            profile.source.axiom_types.insert(name.into(), 1);
            assert!(
                !bounded_near_el_certified_candidate(&profile),
                "{name} must fail the bounded near-EL screen closed"
            );
        }
    }

    #[test]
    fn bounded_near_el_gate_declines_expensive_refusals() {
        // A near-complete disjointness clique carries no positive EL structure
        // to complete and expands quadratically in the class count.
        let mut profile = bounded_near_el_terminology_profile();
        profile.source.disjoint_class_axioms = profile.source.distinct_classes + 1;
        assert!(!bounded_near_el_certified_candidate(&profile));
        profile.source.disjoint_class_axioms = profile.source.distinct_classes;
        assert!(bounded_near_el_certified_candidate(&profile));

        // Deep nesting means long definer chains for the certificate.
        let mut profile = bounded_near_el_terminology_profile();
        profile.source.max_concept_depth = 4;
        assert!(!bounded_near_el_certified_candidate(&profile));
        profile.source.max_concept_depth = 3;
        assert!(bounded_near_el_certified_candidate(&profile));

        // Beyond the refusal budget the exact fallback must not run second.
        let mut profile = bounded_near_el_terminology_profile();
        profile.source.file_bytes = 16 * 1024 * 1024 + 1;
        assert!(!bounded_near_el_certified_candidate(&profile));
        profile.source.file_bytes = 16 * 1024 * 1024;
        assert!(bounded_near_el_certified_candidate(&profile));
    }

    #[test]
    fn bounded_near_el_gate_never_preempts_an_exact_fragment_route() {
        // A non-separable ABox is a nominal source: the EL worker sees clauses,
        // not singleton identity, so it must keep the exact nominal calculus.
        let mut profile = domain_range_near_el_positive_abox_profile();
        profile.positive_abox_tbox_separable = false;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(bounded_near_el_certified_candidate(&profile));
        assert_eq!(select(&profile), Route::Nominals);

        // DL-safe rules keep the validated rule stage.
        let mut profile = bounded_near_el_terminology_profile();
        profile.source.rule_axioms = 1;
        assert_eq!(select(&profile), Route::HtRules);

        // The already-recognized source-EL terminology keeps the bare atomic
        // EL route rather than the certificate-plus-production bundle.
        let mut profile = bounded_near_el_terminology_profile();
        profile.source.unions = 0;
        assert!(source_el_terminology_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);

        // The scoped inverse+cardinality certificate still wins.
        let mut profile = bounded_near_el_terminology_profile();
        profile.inverse_cardinality_role_separable = true;
        assert_eq!(select(&profile), Route::ProductionAll);

        // The established one-worker production refinement keeps priority.
        let mut profile = bounded_near_el_terminology_profile();
        profile.source.file_bytes = 1_000_000;
        profile.source.logical_axioms = 5_000;
        profile.source.distinct_classes = 3_000;
        profile.expressivity.functionality = true;
        assert!(bounded_near_el_certified_candidate(&profile));
        assert!(one_thread_small_production_candidate(&profile));
        assert_eq!(select(&profile), Route::ProductionAll1);
    }

    /// The certified positive-ABox Horn SHIF family (ORE 10127 shape): a large
    /// asserted graph over a small terminology whose only class constructors
    /// are intersection, existential and universal restriction.
    fn positive_abox_horn_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.schema_version = 2;
        profile.positive_abox_tbox_separable = true;
        profile.disjoint_union_abox_candidate = true;
        profile.source.file_bytes = 17_845_208;
        profile.source.logical_axioms = 106_790;
        profile.source.tbox_axioms = 1_227;
        profile.source.rbox_axioms = 15;
        profile.source.abox_axioms = 105_548;
        profile.source.declarations = 710;
        profile.source.declared_classes = 688;
        profile.source.declared_object_properties = 21;
        profile.source.declared_data_properties = 1;
        profile.source.distinct_classes = 688;
        profile.source.distinct_object_properties = 21;
        profile.source.distinct_data_properties = 1;
        profile.source.distinct_individuals = 20_902;
        profile.source.subclass_axioms = 696;
        profile.source.equivalent_class_axioms = 531;
        profile.source.role_inclusion_axioms = 1;
        profile.source.transitive_role_axioms = 3;
        profile.source.functional_role_axioms = 1;
        profile.source.domain_axioms = 4;
        profile.source.range_axioms = 4;
        profile.source.class_assertions = 65_792;
        profile.source.role_assertions = 39_756;
        profile.source.concept_expressions = 70_477;
        profile.source.intersections = 481;
        profile.source.existentials = 969;
        profile.source.universals = 292;
        profile.source.max_concept_depth = 10;
        profile.source.max_concept_arity = 2;
        for (name, count) in [
            ("ClassAssertion", 65_792),
            ("DataPropertyAssertion", 529),
            ("Declaration", 710),
            ("EquivalentClasses", 531),
            ("FunctionalObjectProperty", 1),
            ("InverseObjectProperties", 2),
            ("ObjectPropertyAssertion", 39_227),
            ("ObjectPropertyDomain", 4),
            ("ObjectPropertyRange", 4),
            ("SubClassOf", 696),
            ("SubObjectPropertyOf", 1),
            ("TransitiveObjectProperty", 3),
        ] {
            profile.source.axiom_types.insert(name.into(), count);
        }
        profile.expressivity.negation_disjunction = true;
        profile.expressivity.existential = true;
        profile.expressivity.functionality = true;
        profile.expressivity.role_hierarchy = true;
        profile
    }

    /// A 19-class complete disjointness clique over a large role schema with
    /// functional data properties (ORE 2195 shape). No class constructor at
    /// all, so neither absorption changes its clause set.
    fn disjointness_clique_schema_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.schema_version = 2;
        profile.source.file_bytes = 186_295;
        profile.source.logical_axioms = 1_118;
        profile.source.tbox_axioms = 171;
        profile.source.rbox_axioms = 947;
        profile.source.declarations = 449;
        profile.source.declared_classes = 19;
        profile.source.declared_object_properties = 342;
        profile.source.declared_data_properties = 88;
        profile.source.distinct_classes = 19;
        profile.source.distinct_object_properties = 342;
        profile.source.distinct_data_properties = 88;
        profile.source.disjoint_class_axioms = 171;
        profile.source.functional_role_axioms = 87;
        profile.source.domain_axioms = 430;
        profile.source.range_axioms = 430;
        profile.source.concept_expressions = 1_114;
        profile.source.max_concept_depth = 1;
        for (name, count) in [
            ("DataPropertyDomain", 88),
            ("DataPropertyRange", 88),
            ("Declaration", 449),
            ("DisjointClasses", 171),
            ("FunctionalDataProperty", 87),
            ("ObjectPropertyDomain", 342),
            ("ObjectPropertyRange", 342),
        ] {
            profile.source.axiom_types.insert(name.into(), count);
        }
        profile.expressivity.negation_disjunction = true;
        profile.expressivity.functionality = true;
        profile.expressivity.datatype = true;
        profile
    }

    /// A self-restriction SHIF terminology with a handful of complements and
    /// unqualified cardinalities (ORE 4827 shape). The explicit complements
    /// are what polarity absorption shrinks.
    fn complement_bearing_terminology_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.schema_version = 2;
        profile.source.file_bytes = 191_942;
        profile.source.logical_axioms = 1_125;
        profile.source.tbox_axioms = 1_006;
        profile.source.rbox_axioms = 119;
        profile.source.declarations = 921;
        profile.source.declared_classes = 865;
        profile.source.declared_object_properties = 50;
        profile.source.declared_data_properties = 6;
        profile.source.distinct_classes = 865;
        profile.source.distinct_object_properties = 50;
        profile.source.distinct_data_properties = 6;
        profile.source.subclass_axioms = 964;
        profile.source.equivalent_class_axioms = 41;
        profile.source.disjoint_class_axioms = 1;
        profile.source.role_inclusion_axioms = 51;
        profile.source.domain_axioms = 23;
        profile.source.range_axioms = 45;
        profile.source.concept_expressions = 2_223;
        profile.source.intersections = 39;
        profile.source.unions = 11;
        profile.source.complements = 2;
        profile.source.existentials = 28;
        profile.source.min_cardinalities = 2;
        profile.source.exact_cardinalities = 4;
        profile.source.unqualified_cardinalities = 6;
        profile.source.has_self = 30;
        profile.source.max_concept_depth = 3;
        profile.source.max_concept_arity = 7;
        profile.source.max_cardinality = 1;
        for (name, count) in [
            ("DataPropertyDomain", 2),
            ("Declaration", 921),
            ("DisjointClasses", 1),
            ("EquivalentClasses", 41),
            ("ObjectPropertyDomain", 21),
            ("ObjectPropertyRange", 45),
            ("SubClassOf", 964),
            ("SubDataPropertyOf", 4),
            ("SubObjectPropertyOf", 47),
        ] {
            profile.source.axiom_types.insert(name.into(), count);
        }
        profile.expressivity.negation_disjunction = true;
        profile.expressivity.existential = true;
        profile.expressivity.cardinality = true;
        profile.expressivity.role_hierarchy = true;
        profile
    }

    /// A disjointness-heavy SHIF(D) terminology with one union, a few
    /// universals and unqualified cardinalities (ORE 7901 shape).
    fn union_free_disjointness_terminology_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.schema_version = 2;
        profile.source.file_bytes = 81_109;
        profile.source.logical_axioms = 489;
        profile.source.tbox_axioms = 287;
        profile.source.rbox_axioms = 202;
        profile.source.declarations = 211;
        profile.source.declared_classes = 104;
        profile.source.declared_object_properties = 33;
        profile.source.declared_data_properties = 74;
        profile.source.distinct_classes = 104;
        profile.source.distinct_object_properties = 33;
        profile.source.distinct_data_properties = 74;
        profile.source.subclass_axioms = 117;
        profile.source.disjoint_class_axioms = 170;
        profile.source.role_inclusion_axioms = 14;
        profile.source.transitive_role_axioms = 15;
        profile.source.functional_role_axioms = 43;
        profile.source.domain_axioms = 39;
        profile.source.range_axioms = 80;
        profile.source.concept_expressions = 634;
        profile.source.unions = 1;
        profile.source.existentials = 7;
        profile.source.universals = 3;
        profile.source.exact_cardinalities = 5;
        profile.source.unqualified_cardinalities = 5;
        profile.source.max_concept_depth = 3;
        profile.source.max_concept_arity = 2;
        profile.source.max_cardinality = 1;
        for (name, count) in [
            ("DataPropertyDomain", 33),
            ("DataPropertyRange", 71),
            ("Declaration", 211),
            ("DisjointClasses", 170),
            ("FunctionalDataProperty", 41),
            ("FunctionalObjectProperty", 2),
            ("InverseObjectProperties", 10),
            ("ObjectPropertyDomain", 6),
            ("ObjectPropertyRange", 9),
            ("SubClassOf", 117),
            ("SubDataPropertyOf", 2),
            ("SubObjectPropertyOf", 12),
            ("SymmetricObjectProperty", 1),
            ("TransitiveObjectProperty", 15),
        ] {
            profile.source.axiom_types.insert(name.into(), count);
        }
        profile.expressivity.negation_disjunction = true;
        profile.expressivity.existential = true;
        profile.expressivity.cardinality = true;
        profile.expressivity.functionality = true;
        profile.expressivity.role_hierarchy = true;
        profile.expressivity.datatype = true;
        profile
    }

    #[test]
    fn automatic_route_runs_bare_cb_on_the_positive_abox_horn_family() {
        let profile = positive_abox_horn_profile();
        assert_eq!(semantic_fragment(&profile), SemanticFragment::PositiveAbox);
        assert!(positive_abox_horn_cb_candidate(&profile));
        assert_eq!(select(&profile), Route::CbAbsorb8);
        // The bundle must be the isolated CB mechanism on the same
        // polarity-absorbed clause set the production bundle feeds its CB arm.
        let settings = Route::CbAbsorb8.settings();
        assert!(settings.contains(&("KM_MECHANISM", "cb")));
        assert!(settings.contains(&("KM_ABSORB", "1")));
        assert!(settings.contains(&("KM_THREADS", "8")));

        // The family scales from the smallest to the largest measured member
        // without leaving the screen.
        let mut small = positive_abox_horn_profile();
        small.source.file_bytes = 1_253_294;
        small.source.logical_axioms = 7_465;
        small.source.abox_axioms = 7_169;
        small.source.class_assertions = 4_676;
        small.source.role_assertions = 2_493;
        small.source.distinct_classes = 167;
        small.source.universals = 55;
        small.source.existentials = 179;
        assert_eq!(select(&small), Route::CbAbsorb8);
    }

    #[test]
    fn positive_abox_horn_cb_gate_fails_closed_outside_its_fragment() {
        let cases: [(&str, fn(&mut OntologyProfile)); 14] = [
            ("union", |p| p.source.unions = 1),
            ("complement", |p| p.source.complements = 1),
            ("disjointness", |p| p.source.disjoint_class_axioms = 1),
            ("min cardinality", |p| p.source.min_cardinalities = 1),
            ("max cardinality", |p| p.source.max_cardinalities = 1),
            ("exact cardinality", |p| p.source.exact_cardinalities = 1),
            ("class bottom", |p| p.source.bottom_occurrences = 1),
            ("nominal", |p| p.source.nominals = 1),
            ("hasValue", |p| p.source.has_values = 1),
            ("hasSelf", |p| p.source.has_self = 1),
            ("bottom role", |p| p.source.bottom_role_occurrences = 1),
            ("import", |p| p.source.imports = 1),
            ("rule", |p| p.source.rule_axioms = 1),
            ("unsupported rule", |p| p.source.unsupported_rule_axioms = 1),
        ];
        for (label, mutate) in cases {
            let mut profile = positive_abox_horn_profile();
            mutate(&mut profile);
            assert!(
                !positive_abox_horn_cb_candidate(&profile),
                "{label} must fail the positive-ABox Horn screen closed"
            );
            assert_ne!(
                select(&profile),
                Route::CbAbsorb8,
                "{label} must not reach the isolated CB bundle"
            );
        }

        for name in [
            "NegativeObjectPropertyAssertion",
            "NegativeDataPropertyAssertion",
            "SameIndividual",
            "DifferentIndividuals",
        ] {
            let mut profile = positive_abox_horn_profile();
            profile.source.axiom_types.insert(name.into(), 1);
            assert!(
                !positive_abox_horn_cb_candidate(&profile),
                "{name} must fail the positive-ABox Horn screen closed"
            );
        }

        // Inside the EL class fragment the portfolio's EL arm can answer, so
        // the source keeps its established route.
        let mut profile = positive_abox_horn_profile();
        profile.source.universals = 0;
        assert!(!positive_abox_horn_cb_candidate(&profile));

        // A flat identity ABox is the independent-ABox family, not this one.
        let mut profile = positive_abox_horn_profile();
        profile.source.role_assertions = 0;
        assert!(!positive_abox_horn_cb_candidate(&profile));

        // Beyond the attempt budget the un-retried CB bundle must not run.
        let mut profile = positive_abox_horn_profile();
        profile.source.file_bytes = 128 * 1024 * 1024 + 1;
        assert!(!positive_abox_horn_cb_candidate(&profile));
        profile.source.file_bytes = 128 * 1024 * 1024;
        assert!(positive_abox_horn_cb_candidate(&profile));
    }

    #[test]
    fn positive_abox_horn_cb_gate_never_preempts_an_exact_fragment_route() {
        // Without the positive separation certificate this is an ordinary
        // nominal ABox. The source shape still passes the screen, but the
        // nominal branch is reached first and keeps a route that carries the
        // exact singleton-aware CB fallback.
        let mut profile = positive_abox_horn_profile();
        profile.positive_abox_tbox_separable = false;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(positive_abox_horn_cb_candidate(&profile));
        assert_eq!(select(&profile), Route::CertifiedNominals);
        assert!(Route::CertifiedNominals
            .settings()
            .contains(&("KM_NOMINALS", "1")));

        // DL-safe rules keep the validated rule stage.
        let mut profile = positive_abox_horn_profile();
        profile.source.rule_axioms = 1;
        assert_eq!(select(&profile), Route::HtRules);

        // The scoped inverse+cardinality certificate still wins.
        let mut profile = positive_abox_horn_profile();
        profile.inverse_cardinality_role_separable = true;
        assert_eq!(select(&profile), Route::ProductionAll);
    }

    #[test]
    fn automatic_route_runs_bare_cb_on_bounded_non_el_terminologies() {
        for (profile, expected) in [
            (disjointness_clique_schema_profile(), Route::CbPlain1),
            (complement_bearing_terminology_profile(), Route::CbAbsorb8),
            (
                union_free_disjointness_terminology_profile(),
                Route::CbTrigger16,
            ),
        ] {
            assert_eq!(semantic_fragment(&profile), SemanticFragment::SriqCore);
            assert!(
                bounded_non_el_cb_terminology_candidate(&profile),
                "the bounded non-EL screen must admit this terminology"
            );
            assert!(
                !bounded_near_el_certified_candidate(&profile),
                "the certified EL screen must not already cover it"
            );
            assert_eq!(bounded_non_el_cb_terminology_route(&profile), expected);
            assert_eq!(select(&profile), expected);
            assert!(expected.settings().contains(&("KM_MECHANISM", "cb")));
        }
    }

    #[test]
    fn bounded_non_el_cb_gate_requires_a_construct_outside_the_el_class_fragment() {
        // Named disjointness alone is an EL constraint (`elc` represents it as
        // an NF5 empty-head clause), so the portfolio's EL arm can decide this
        // terminology and must keep the chance to.
        let mut profile = disjointness_clique_schema_profile();
        profile.source.functional_role_axioms = 0;
        profile.source.axiom_types.remove("FunctionalDataProperty");
        assert!(!bounded_non_el_cb_terminology_candidate(&profile));
        assert_ne!(select(&profile), Route::CbPlain1);

        // Any one of the constructors that is outside EL in every position
        // re-admits it.
        let outside: [(&str, fn(&mut OntologyProfile)); 5] = [
            ("universal", |p| p.source.universals = 1),
            ("min cardinality", |p| p.source.min_cardinalities = 1),
            ("max cardinality", |p| p.source.max_cardinalities = 1),
            ("exact cardinality", |p| p.source.exact_cardinalities = 1),
            ("inverse functionality", |p| {
                p.source.inverse_functional_role_axioms = 1
            }),
        ];
        for (label, mutate) in outside {
            let mut readmitted = profile.clone();
            mutate(&mut readmitted);
            assert!(
                bounded_non_el_cb_terminology_candidate(&readmitted),
                "{label} places the source outside the EL class fragment"
            );
        }
    }

    #[test]
    fn bounded_non_el_cb_gate_fails_closed_on_density_size_and_nominals() {
        // More than one union per hundred logical axioms is live disjunction,
        // which is exactly what the isolated CB bundles lose on.
        let mut profile = complement_bearing_terminology_profile();
        profile.source.unions = 12;
        assert!(!bounded_non_el_cb_terminology_candidate(&profile));
        profile.source.unions = 11;
        assert!(bounded_non_el_cb_terminology_candidate(&profile));

        let mut profile = complement_bearing_terminology_profile();
        profile.source.complements = 12;
        assert!(!bounded_non_el_cb_terminology_candidate(&profile));

        // Above the attempt bounds the portfolio's other arms start deciding
        // terminologies the CB engine alone cannot.
        let mut profile = complement_bearing_terminology_profile();
        profile.source.logical_axioms = 2_001;
        assert!(!bounded_non_el_cb_terminology_candidate(&profile));
        profile.source.logical_axioms = 2_000;
        assert!(bounded_non_el_cb_terminology_candidate(&profile));

        let mut profile = complement_bearing_terminology_profile();
        profile.source.file_bytes = 512 * 1024 + 1;
        assert!(!bounded_non_el_cb_terminology_candidate(&profile));
        profile.source.file_bytes = 512 * 1024;
        assert!(bounded_non_el_cb_terminology_candidate(&profile));

        // The trivial band keeps its established route.
        let mut profile = union_free_disjointness_terminology_profile();
        profile.source.logical_axioms = 99;
        assert!(!bounded_non_el_cb_terminology_candidate(&profile));

        let cases: [(&str, fn(&mut OntologyProfile)); 6] = [
            ("nominal", |p| p.source.nominals = 1),
            ("hasValue", |p| p.source.has_values = 1),
            ("bottom role", |p| p.source.bottom_role_occurrences = 1),
            ("import", |p| p.source.imports = 1),
            ("rule", |p| p.source.rule_axioms = 1),
            ("unsupported rule", |p| p.source.unsupported_rule_axioms = 1),
        ];
        for (label, mutate) in cases {
            let mut profile = union_free_disjointness_terminology_profile();
            mutate(&mut profile);
            assert!(
                !bounded_non_el_cb_terminology_candidate(&profile),
                "{label} must fail the bounded non-EL screen closed"
            );
            assert_ne!(select(&profile), Route::CbTrigger16, "{label}");
        }

        for name in [
            "NegativeObjectPropertyAssertion",
            "NegativeDataPropertyAssertion",
        ] {
            let mut profile = union_free_disjointness_terminology_profile();
            profile.source.axiom_types.insert(name.into(), 1);
            assert!(!bounded_non_el_cb_terminology_candidate(&profile));
        }
    }

    #[test]
    fn bounded_non_el_cb_gate_never_preempts_an_exact_fragment_route() {
        // Any ABox leaves the nominal-free fragment this screen is scoped to.
        let mut profile = union_free_disjointness_terminology_profile();
        profile.source.abox_axioms = 1;
        profile.source.class_assertions = 1;
        assert!(!bounded_non_el_cb_terminology_candidate(&profile));
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert_eq!(select(&profile), Route::Nominals);

        // DL-safe rules keep the validated rule stage.
        let mut profile = union_free_disjointness_terminology_profile();
        profile.source.rule_axioms = 1;
        assert_eq!(select(&profile), Route::HtRules);

        // The scoped inverse+cardinality certificate still wins.
        let mut profile = union_free_disjointness_terminology_profile();
        profile.inverse_cardinality_role_separable = true;
        assert_eq!(select(&profile), Route::ProductionAll);

        // The established one-worker production refinement keeps priority.
        let mut profile = complement_bearing_terminology_profile();
        profile.source.logical_axioms = 1_900;
        profile.source.distinct_classes = 2_500;
        profile.expressivity.functionality = true;
        profile.expressivity.cardinality = false;
        assert!(bounded_non_el_cb_terminology_candidate(&profile));
        assert!(one_thread_small_production_candidate(&profile));
        assert_eq!(select(&profile), Route::ProductionAll1);
    }

    #[test]
    fn bare_cb_routes_keep_the_exact_production_fallback() {
        // These bundles set `KM_NO_RETRY=1`, so a worker error, a non-fixpoint
        // exit, or an RSS trip has to return to the route the screen displaced.
        for route in [Route::CbAbsorb8, Route::CbPlain1, Route::CbTrigger16] {
            assert!(route.settings().contains(&("KM_NO_RETRY", "1")));
            assert_eq!(
                automatic_atomic_fallback(route, &union_free_disjointness_terminology_profile()),
                Some(Route::ProductionAll)
            );
            assert_eq!(
                automatic_atomic_fallback(route, &positive_abox_horn_profile()),
                Some(Route::ProductionAll)
            );
            let mut nominal = positive_abox_horn_profile();
            nominal.positive_abox_tbox_separable = false;
            assert_eq!(
                automatic_atomic_fallback(route, &nominal),
                Some(Route::Nominals)
            );
        }
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
        assert!(Route::HtGeneral.settings().contains(&("KM_HT_FORCE", "1")));
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
        source
            .axiom_types
            .insert("DataPropertyAssertion".into(), 624);
        source.axiom_types.insert("DifferentIndividuals".into(), 1);
        source
            .axiom_types
            .insert("InverseObjectProperties".into(), 21);

        assert!(ground_clause_general_ht_candidate(&profile));
        assert_eq!(select(&profile), Route::HtGeneral);
        profile.source.class_assertions += 1;
        assert!(!ground_clause_general_ht_candidate(&profile));
    }

    #[test]
    fn compact_nominal_profile_schedules_certified_general_ht() {
        let mut profile = OntologyProfile::default();
        profile.expressivity.nominal_individual = true;
        profile.source.logical_axioms = 7_000;
        profile.source.tbox_axioms = 4_000;
        profile.source.abox_axioms = 2_000;
        profile.source.role_assertions = 600;
        profile.source.unions = 2;

        assert!(compact_nominal_general_ht_candidate(&profile));
        assert_eq!(select(&profile), Route::HtGeneral);

        profile.source.complements = 1;
        assert!(!compact_nominal_general_ht_candidate(&profile));
        assert_eq!(select(&profile), Route::Nominals);

        profile.source.complements = 0;
        profile.source.unions = 0;
        profile.source.role_assertions = 399;
        assert!(!compact_nominal_general_ht_candidate(&profile));
        assert_eq!(select(&profile), Route::Nominals);

        profile.source.unions = 2;
        profile.source.role_assertions = 0;
        assert!(!compact_nominal_general_ht_candidate(&profile));
        assert_eq!(select(&profile), Route::Nominals);
    }

    #[test]
    fn large_card_profile_schedules_certified_general_ht() {
        let mut profile = OntologyProfile::default();
        profile.card_number_role_separable = true;
        profile.source.logical_axioms = 11_821;
        profile.source.tbox_axioms = 11_455;
        profile.source.abox_axioms = 223;
        profile.source.unions = 381;
        profile.source.qualified_cardinalities = 1;
        profile.source.role_chain_axioms = 6;

        assert!(large_card_general_ht_candidate(&profile));
        assert_eq!(select(&profile), Route::HtGeneral);

        profile.source.logical_axioms = 2_168;
        profile.source.abox_axioms = 2_004;
        profile.source.unions = 9;
        profile.source.role_chain_axioms = 0;
        assert!(!large_card_general_ht_candidate(&profile));
        assert_eq!(select(&profile), Route::CertifiedCardProxyAbox);
    }

    #[test]
    fn high_unqualified_cardinality_profile_schedules_shoq() {
        let mut profile = OntologyProfile::default();
        profile.expressivity.nominal = true;
        profile.expressivity.nominal_individual = true;
        profile.expressivity.cardinality = true;
        profile.expressivity.inverse = true;
        profile.source.max_cardinality = 300;
        profile.source.exact_cardinalities = 1;
        profile.source.min_cardinalities = 5;
        profile.source.unqualified_cardinalities = 6;
        profile.source.nominals = 63;

        assert!(high_unqualified_cardinality_shoq_candidate(&profile));
        assert_eq!(select(&profile), Route::HtShoq);

        profile.source.qualified_cardinalities = 1;
        profile.expressivity.qualified_cardinality = true;
        assert!(!high_unqualified_cardinality_shoq_candidate(&profile));
        assert_ne!(select(&profile), Route::HtShoq);
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
        assert_eq!(select(&profile), Route::CertifiedNominals);

        // The same no-cardinality family begins at ORE8480's measured scale.
        let mut medium = profile.clone();
        medium.source.abox_axioms = 41_814;
        medium.source.class_assertions = 19_184;
        medium.source.role_assertions = 10_462;
        medium.source.distinct_individuals = 24_910;
        assert!(large_no_cardinality_abox_production_candidate(&medium));
        assert_eq!(select(&medium), Route::CertifiedNominals);

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
    fn compact_role_rich_tbox_uses_fail_closed_ht_bridge() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 1_675;
        profile.source.distinct_object_properties = 215;
        profile.source.universals = 406;
        profile.clauses.clauses = 2_942;
        profile.expressivity.inverse = true;
        profile.expressivity.transitivity = true;
        profile.expressivity.negation_disjunction = true;
        assert!(compact_role_rich_ht_bridge_candidate(&profile));
        assert_eq!(select(&profile), Route::HtBridge);
        assert_eq!(
            automatic_atomic_fallback(Route::HtBridge, &profile),
            Some(Route::ProductionAll)
        );

        profile.source.role_chain_axioms = 1;
        assert!(!compact_role_rich_ht_bridge_candidate(&profile));
    }

    #[test]
    fn compact_normalized_families_use_fail_closed_ht_bridge() {
        let mut qualified = OntologyProfile::default();
        qualified.source.logical_axioms = 178;
        qualified.source.qualified_cardinalities = 37;
        qualified.clauses.clauses = 596;
        assert!(compact_normalized_ht_bridge_candidate(&qualified));
        assert_eq!(select(&qualified), Route::HtBridge);

        let mut role_dense = OntologyProfile::default();
        role_dense.source.logical_axioms = 444;
        role_dense.source.distinct_classes = 132;
        role_dense.source.distinct_object_properties = 132;
        role_dense.source.existentials = 74;
        assert!(compact_normalized_ht_bridge_candidate(&role_dense));

        let mut horn_shi = OntologyProfile::default();
        horn_shi.source.logical_axioms = 2_790;
        horn_shi.source.distinct_classes = 2_291;
        horn_shi.source.distinct_object_properties = 17;
        horn_shi.source.intersections = 193;
        horn_shi.source.existentials = 219;
        horn_shi.source.max_concept_depth = 3;
        horn_shi.clauses.clauses = 3_829;
        horn_shi.expressivity.inverse = true;
        horn_shi.expressivity.transitivity = true;
        assert!(compact_normalized_ht_bridge_candidate(&horn_shi));
        assert_eq!(select(&horn_shi), Route::HtBridge);
        horn_shi.source.max_concept_depth = 4;
        assert!(!compact_normalized_ht_bridge_candidate(&horn_shi));

        let mut role_schema = OntologyProfile::default();
        role_schema.source.logical_axioms = 967;
        role_schema.source.distinct_classes = 84;
        role_schema.source.distinct_object_properties = 260;
        role_schema.source.domain_axioms = 256;
        role_schema.source.range_axioms = 254;
        role_schema.source.inverse_functional_role_axioms = 8;
        role_schema.clauses.clauses = 1_403;
        role_schema.expressivity.inverse = true;
        role_schema.expressivity.functionality = true;
        assert!(compact_normalized_ht_bridge_candidate(&role_schema));
        assert_eq!(select(&role_schema), Route::HtBridge);
        role_schema.expressivity.functionality = false;
        assert!(!compact_normalized_ht_bridge_candidate(&role_schema));

        let mut el_lookalike = OntologyProfile::default();
        el_lookalike.source.logical_axioms = 1_627;
        el_lookalike.source.distinct_classes = 709;
        el_lookalike.source.distinct_object_properties = 8;
        el_lookalike.source.existentials = 921;
        assert!(!compact_normalized_ht_bridge_candidate(&el_lookalike));

        qualified.source.abox_axioms = 1;
        assert!(!compact_normalized_ht_bridge_candidate(&qualified));
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
    fn heap_trim_is_limited_to_the_measured_small_nominal_worker_shape() {
        let mut profile = OntologyProfile::default();
        profile.expressivity.code = "SHOI".into();
        profile.expressivity.nominal = true;
        profile.source.logical_axioms = 2_171;
        profile.source.distinct_classes = 1_269;
        profile.source.distinct_object_properties = 141;
        profile.source.distinct_individuals = 210;
        profile.source.abox_axioms = 211;
        profile.source.nominals = 161;
        profile.source.file_bytes = 412_646;
        assert!(small_nominal_heap_trim_candidate(&profile));

        profile.expressivity.code = "SHOIF(D)".into();
        assert!(!small_nominal_heap_trim_candidate(&profile));
        profile.expressivity.code = "SHOI".into();
        profile.source.logical_axioms = 864;
        assert!(!small_nominal_heap_trim_candidate(&profile));
        profile.source.logical_axioms = 2_171;
        profile.source.rule_axioms = 1;
        assert!(!small_nominal_heap_trim_candidate(&profile));
    }

    #[test]
    fn compact_nominal_worker_schedule_is_bounded_by_source_shape() {
        let mut profile = OntologyProfile::default();
        profile.source.file_bytes = 96_360;
        profile.source.logical_axioms = 530;
        profile.source.abox_axioms = 298;
        profile.source.max_concept_depth = 2;
        profile.source.distinct_classes = 35;
        assert!(one_thread_compact_nominal_candidate(&profile));

        let invalidators: [fn(&mut OntologyProfile); 6] = [
            |p: &mut OntologyProfile| p.source.file_bytes = 170_001,
            |p: &mut OntologyProfile| p.source.logical_axioms = 299,
            |p: &mut OntologyProfile| p.source.abox_axioms = 321,
            |p: &mut OntologyProfile| p.source.max_concept_depth = 4,
            |p: &mut OntologyProfile| p.source.distinct_classes = 301,
            |p: &mut OntologyProfile| p.source.rule_axioms = 1,
        ];
        for mutate in invalidators {
            let mut rejected = profile.clone();
            mutate(&mut rejected);
            assert!(!one_thread_compact_nominal_candidate(&rejected));
        }
    }

    #[test]
    fn compact_nominal_worker_gate_carries_no_ontology_identity() {
        let source = include_str!("routing.rs");
        let start = source
            .find("pub(crate) fn one_thread_compact_nominal_candidate")
            .expect("the compact nominal worker gate is present");
        let body = &source[start..];
        let end = body.find("\n}\n").expect("the gate has a body");
        assert!(!body[..end].contains("ore_ont_"));
    }

    /// Corpus projection for the compact exact-nominal worker schedule.
    /// Ordinary tests remain artifact-independent; release validation supplies
    /// the retained 592-profile directory explicitly.
    #[test]
    fn compact_nominal_worker_projection_over_retained_profiles() {
        #[derive(serde::Deserialize)]
        struct Record {
            ont: String,
            profile: OntologyProfile,
        }

        let Some(dir) = std::env::var_os("KM_NOMINAL_WORKER_PROFILE_DIR") else {
            return;
        };
        let mut entries: Vec<std::path::PathBuf> = std::fs::read_dir(dir)
            .expect("profile directory")
            .map(|entry| entry.expect("profile entry").path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
            .collect();
        entries.sort();
        let mut armed = Vec::new();
        for path in &entries {
            let record: Record =
                serde_json::from_str(&std::fs::read_to_string(path).expect("profile record"))
                    .expect("profile record shape");
            if select(&record.profile) == Route::Nominals
                && one_thread_compact_nominal_candidate(&record.profile)
            {
                armed.push(record.ont);
            }
        }
        assert_eq!(entries.len(), 592, "the retained corpus has 592 profiles");
        assert_eq!(
            armed.len(),
            4,
            "unexpected compact nominal projection: {armed:?}"
        );
    }

    #[test]
    fn source_nominal_free_ht_schedule_is_bounded_by_source_shape() {
        let mut profile = OntologyProfile::default();
        profile.source.file_bytes = 147_634;
        profile.source.logical_axioms = 702;
        profile.source.abox_axioms = 258;
        profile.source.max_concept_depth = 4;
        profile.source.distinct_classes = 112;
        assert!(one_worker_source_nominal_free_ht_candidate(&profile));

        let invalidators: [fn(&mut OntologyProfile); 9] = [
            |p: &mut OntologyProfile| p.source.file_bytes = 170_001,
            |p: &mut OntologyProfile| p.source.logical_axioms = 299,
            |p: &mut OntologyProfile| p.source.abox_axioms = 321,
            |p: &mut OntologyProfile| p.source.max_concept_depth = 5,
            |p: &mut OntologyProfile| p.source.distinct_classes = 401,
            |p: &mut OntologyProfile| p.source.nominals = 1,
            |p: &mut OntologyProfile| p.source.imports = 1,
            |p: &mut OntologyProfile| p.source.rule_axioms = 1,
            |p: &mut OntologyProfile| p.source.unsupported_rule_axioms = 1,
        ];
        for mutate in invalidators {
            let mut rejected = profile.clone();
            mutate(&mut rejected);
            assert!(!one_worker_source_nominal_free_ht_candidate(&rejected));
        }

        let mut exact_cb_envelope = profile;
        exact_cb_envelope.source.max_concept_depth = 3;
        exact_cb_envelope.source.distinct_classes = 100;
        assert!(one_thread_compact_nominal_candidate(&exact_cb_envelope));
        assert!(!one_worker_source_nominal_free_ht_candidate(
            &exact_cb_envelope
        ));
    }

    #[test]
    fn source_nominal_free_ht_gate_carries_no_ontology_identity() {
        let source = include_str!("routing.rs");
        let start = source
            .find("pub(crate) fn one_worker_source_nominal_free_ht_candidate")
            .expect("the source-nominal-free HT gate is present");
        let body = &source[start..];
        let end = body.find("\n}\n").expect("the gate has a body");
        assert!(!body[..end].contains("ore_ont_"));
    }

    /// Corpus projection for the one-worker complete-HT nominal probe.
    /// Release validation supplies the retained 592-profile directory.
    #[test]
    fn source_nominal_free_ht_projection_over_retained_profiles() {
        #[derive(serde::Deserialize)]
        struct Record {
            ont: String,
            profile: OntologyProfile,
        }

        let Some(dir) = std::env::var_os("KM_NOMINAL_WORKER_PROFILE_DIR") else {
            return;
        };
        let mut entries: Vec<std::path::PathBuf> = std::fs::read_dir(dir)
            .expect("profile directory")
            .map(|entry| entry.expect("profile entry").path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
            .collect();
        entries.sort();
        let mut armed = Vec::new();
        for path in &entries {
            let record: Record =
                serde_json::from_str(&std::fs::read_to_string(path).expect("profile record"))
                    .expect("profile record shape");
            if matches!(
                select(&record.profile),
                Route::Nominals | Route::CertifiedNominals
            ) && one_worker_source_nominal_free_ht_candidate(&record.profile)
            {
                armed.push(record.ont);
            }
        }
        assert_eq!(entries.len(), 592, "the retained corpus has 592 profiles");
        armed.sort();
        assert_eq!(
            armed,
            [
                "ore_ont_13383.owl",
                "ore_ont_2860.owl",
                "ore_ont_5564.owl",
                "ore_ont_9557.owl",
            ],
            "unexpected source-nominal-free HT projection"
        );
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
    fn small_horn_class_abox_uses_plain_cb_schedule() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 2_464;
        profile.source.tbox_axioms = 2_434;
        profile.source.abox_axioms = 11;
        profile.source.class_assertions = 11;
        profile.source.transitive_role_axioms = 7;
        profile.source.role_inclusion_axioms = 8;
        profile.disjoint_union_abox_candidate = true;
        assert!(small_horn_abox_plain_cb_candidate(&profile));

        profile.source.role_assertions = 1;
        assert!(!small_horn_abox_plain_cb_candidate(&profile));
        profile.source.role_assertions = 0;
        profile.source.unions = 1;
        assert!(!small_horn_abox_plain_cb_candidate(&profile));
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
        assert_eq!(select(&profile), Route::CertifiedNominals);
        assert!(!certified_nominal_production_probe_candidate(&profile));
        assert!(certified_nominal_general_ht_probe_candidate(&profile));
    }

    #[test]
    fn compact_shoin_object_abox_tries_the_exact_bridge_first() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 284;
        profile.source.abox_axioms = 49;
        profile.source.class_assertions = 31;
        profile.source.role_assertions = 17;
        profile.source.distinct_classes = 82;
        profile.source.max_concept_depth = 7;
        profile.clauses.clauses = 930;
        profile
            .source
            .axiom_types
            .insert("ClassAssertion".into(), 31);
        profile
            .source
            .axiom_types
            .insert("ObjectPropertyAssertion".into(), 17);
        profile
            .source
            .axiom_types
            .insert("DifferentIndividuals".into(), 1);
        profile.expressivity.inverse = true;
        profile.expressivity.transitivity = true;
        profile.expressivity.cardinality = true;
        profile.expressivity.nominal = true;

        assert!(compact_typed_bridge_first_candidate(&profile));
        profile.source.max_concept_depth = 4;
        assert!(!compact_typed_bridge_first_candidate(&profile));
        profile.source.max_concept_depth = 7;
        profile.source.logical_axioms = 1_001;
        assert!(!compact_typed_bridge_first_candidate(&profile));
    }

    #[test]
    fn flat_role_rich_abox_tries_complete_ht_before_nominal_cb() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 521;
        profile.source.abox_axioms = 382;
        profile.source.distinct_object_properties = 78;
        profile.source.role_assertions = 165;
        profile.source.has_values = 72;
        profile.source.max_concept_depth = 1;
        profile.clauses.clauses = 557;

        assert!(compact_role_assertion_general_ht_candidate(&profile));
        assert_eq!(select(&profile), Route::HtGeneral);

        profile.source.role_chain_axioms = 1;
        assert!(!compact_role_assertion_general_ht_candidate(&profile));
        profile.source.role_chain_axioms = 0;
        profile.source.max_concept_depth = 2;
        assert!(!compact_role_assertion_general_ht_candidate(&profile));
    }

    #[test]
    fn compact_expressive_object_abox_uses_four_ht_workers() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 487;
        profile.source.abox_axioms = 93;
        profile.source.class_assertions = 17;
        profile.source.role_assertions = 76;
        profile.source.distinct_classes = 161;
        profile.source.distinct_object_properties = 57;
        profile.source.max_concept_depth = 4;
        profile.clauses.clauses = 825;
        profile
            .source
            .axiom_types
            .insert("ClassAssertion".into(), 17);
        profile
            .source
            .axiom_types
            .insert("ObjectPropertyAssertion".into(), 76);
        profile.expressivity.inverse = true;
        profile.expressivity.transitivity = true;
        profile.expressivity.cardinality = true;
        profile.expressivity.nominal = true;

        assert!(four_worker_compact_expressive_ht_candidate(&profile));
        profile.source.max_concept_depth = 5;
        assert!(!four_worker_compact_expressive_ht_candidate(&profile));
    }

    #[test]
    fn compact_datatype_has_value_abox_uses_three_ht_workers() {
        let mut profile = OntologyProfile::default();
        profile.source.logical_axioms = 171;
        profile.source.abox_axioms = 6;
        profile.source.class_assertions = 5;
        profile.source.role_assertions = 1;
        profile.source.distinct_classes = 96;
        profile.source.distinct_object_properties = 21;
        profile.source.distinct_data_properties = 6;
        profile.source.max_concept_depth = 3;
        profile.source.has_values = 3;
        // Automatic source routing has not populated normalized clause counts.
        profile.clauses.clauses = 0;
        profile
            .source
            .axiom_types
            .insert("ClassAssertion".into(), 5);
        profile
            .source
            .axiom_types
            .insert("ObjectPropertyAssertion".into(), 1);
        profile.expressivity.datatype = true;
        profile.expressivity.inverse = true;
        profile.expressivity.transitivity = true;
        profile.expressivity.cardinality = true;

        assert!(three_worker_compact_datatype_ht_candidate(&profile));
        profile.source.distinct_data_properties = 0;
        assert!(!three_worker_compact_datatype_ht_candidate(&profile));
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

        // Symmetric role declarations are admitted only as a source-side
        // scheduling hint. Their normalized paired inclusions still face the
        // atomic ELC fragment checker before an answer can be published.
        profile
            .source
            .axiom_types
            .insert("SymmetricObjectProperty".into(), 5);
        assert!(source_el_terminology_candidate(&profile));
        assert_eq!(select(&profile), Route::Elc);
        profile.source.axiom_types.remove("SymmetricObjectProperty");

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
    fn inverse_chain_el_family_uses_complete_bridge_with_exact_fallback() {
        let mut profile = OntologyProfile::default();
        profile.expressivity.inverse = true;
        profile.expressivity.complex_subrole = true;
        profile.source.logical_axioms = 16_635;
        profile.source.tbox_axioms = 16_570;
        profile.source.rbox_axioms = 65;
        profile.source.distinct_classes = 8_008;
        profile.source.disjoint_class_axioms = 65;
        profile.source.existentials = 10_275;
        profile.source.role_chain_axioms = 12;

        assert!(inverse_chain_el_bridge_candidate(&profile));
        assert_eq!(select(&profile), Route::HtBridge);
        assert_eq!(
            automatic_atomic_fallback(Route::HtBridge, &profile),
            Some(Route::ProductionAll)
        );

        // The class-assertion-only variant uses the same complete bridge, but
        // a defer must preserve the independent-ABox production certificate.
        profile.source.logical_axioms += 45_179;
        profile.source.abox_axioms = 45_179;
        profile.source.class_assertions = 45_179;
        profile.source.distinct_individuals = 45_179;
        assert!(independent_large_abox_candidate(&profile));
        assert!(inverse_chain_el_bridge_candidate(&profile));
        assert_eq!(select(&profile), Route::HtBridge);
        assert_eq!(
            automatic_atomic_fallback(Route::HtBridge, &profile),
            Some(Route::ProductionAll)
        );

        let mut nonseparable = profile.clone();
        nonseparable.source.role_assertions = 1;
        nonseparable.source.abox_axioms += 1;
        assert!(!inverse_chain_el_bridge_candidate(&nonseparable));

        let mut disjunctive = profile;
        disjunctive.source.unions = 1;
        assert!(!inverse_chain_el_bridge_candidate(&disjunctive));
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
    fn large_data_assertion_abox_without_cardinality_keeps_nominal_fallback() {
        let mut profile = OntologyProfile::default();
        profile.source.abox_axioms = 607_933;
        profile.source.class_assertions = 382_511;
        profile.source.role_assertions = 225_420;
        profile.source.distinct_individuals = 116_325;
        profile.source.declared_data_properties = 1;
        profile.source.distinct_data_properties = 1;
        profile.source.nominals = 19;
        profile.source.datatype_constructors = 0;
        profile
            .source
            .axiom_types
            .insert("DataPropertyAssertion".to_string(), 996);
        profile.expressivity.nominal = true;
        profile.expressivity.nominal_individual = true;
        profile.expressivity.datatype = false;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(large_no_cardinality_abox_production_candidate(&profile));
        assert_eq!(select(&profile), Route::CertifiedNominals);
        assert!(!certified_nominal_production_probe_candidate(&profile));
        assert!(certified_nominal_general_ht_probe_candidate(&profile));

        profile.source.min_cardinalities = 1;
        profile.expressivity.cardinality = true;
        assert!(!large_no_cardinality_abox_production_candidate(&profile));
        assert!(!certified_nominal_production_probe_candidate(&profile));
        assert!(!certified_nominal_general_ht_probe_candidate(&profile));
    }

    #[test]
    fn large_identity_nominal_abox_gets_complete_general_ht_probe() {
        let mut profile = OntologyProfile::default();
        profile.source.abox_axioms = 256_427;
        profile.source.class_assertions = 111_561;
        profile.source.role_assertions = 78_441;
        profile.source.distinct_individuals = 129_647;
        profile.source.nominals = 18;
        profile
            .source
            .axiom_types
            .insert("SameIndividual".to_string(), 66_423);
        profile.expressivity.nominal = true;
        profile.expressivity.nominal_individual = true;

        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert_eq!(select(&profile), Route::CertifiedNominals);
        assert!(large_identity_nominal_abox_general_ht_candidate(&profile));
        assert!(certified_nominal_general_ht_probe_candidate(&profile));

        profile
            .source
            .axiom_types
            .insert("SameIndividual".to_string(), 9_999);
        assert!(!large_identity_nominal_abox_general_ht_candidate(&profile));
        assert!(!certified_nominal_general_ht_probe_candidate(&profile));

        profile
            .source
            .axiom_types
            .insert("SameIndividual".to_string(), 66_423);
        profile.source.nominals = 0;
        assert!(!large_identity_nominal_abox_general_ht_candidate(&profile));
        assert!(!certified_nominal_general_ht_probe_candidate(&profile));
    }

    #[test]
    fn compact_abox_shapes_get_fail_closed_general_ht_probe() {
        let mut profile = OntologyProfile::default();
        profile.source.abox_axioms = 600;
        profile.source.tbox_axioms = 1_900;
        profile.source.distinct_classes = 1_700;
        profile.source.max_concept_depth = 4;
        profile.clauses.clauses = 2_500;
        profile.clauses.disjunctive_clauses = 10;
        assert!(compact_abox_general_ht_candidate(&profile));

        let mut complement_heavy = profile.clone();
        complement_heavy.source.distinct_classes = 3_700;
        complement_heavy.clauses.disjunctive_clauses = 100;
        assert!(!compact_abox_general_ht_candidate(&complement_heavy));

        let mut assertion_dominated = OntologyProfile::default();
        assertion_dominated.source.abox_axioms = 220_000;
        assertion_dominated.source.tbox_axioms = 40;
        assertion_dominated.source.max_concept_depth = 1;
        assertion_dominated.clauses.clauses = 600;
        assert!(compact_abox_general_ht_candidate(&assertion_dominated));

        assertion_dominated.source.role_chain_axioms = 1;
        assert!(!compact_abox_general_ht_candidate(&assertion_dominated));
    }

    #[test]
    fn small_class_identity_abox_uses_exact_nominal_route() {
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
        assert_eq!(select(&profile), Route::Nominals);
        assert!(certified_nominal_production_probe_candidate(&profile));
        assert!(certified_nominal_general_ht_probe_candidate(&profile));

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
    fn large_tbox_small_identity_abox_uses_certified_nominal_portfolio() {
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
        assert_eq!(select(&profile), Route::CertifiedNominals);

        profile.source.tbox_axioms -= 1;
        assert!(!large_tbox_small_identity_abox_production_candidate(
            &profile
        ));
        assert_eq!(select(&profile), Route::Nominals);
    }

    #[test]
    fn vacuous_top_role_object_abox_uses_the_certified_typed_bridge() {
        // Inverse/complement SHOI terminology of roughly 8,600 axioms with a
        // compact positive object ABox whose roles are read by the TBox: the
        // ORE 16303 feature shape. No projection certificate applies.
        let mut profile = OntologyProfile::default();
        profile.expressivity.code = "SHOI".into();
        profile.expressivity.negation_disjunction = true;
        profile.expressivity.existential = true;
        profile.expressivity.role_hierarchy = true;
        profile.expressivity.nominal = true;
        profile.expressivity.nominal_individual = true;
        profile.source.logical_axioms = 8_600;
        profile.source.tbox_axioms = 8_250;
        profile.source.rbox_axioms = 190;
        profile.source.subclass_axioms = 8_250;
        profile.source.role_inclusion_axioms = 147;
        profile.source.distinct_classes = 4_200;
        profile.source.distinct_object_properties = 156;
        profile.source.distinct_individuals = 151;
        profile.source.existentials = 3_300;
        profile.source.complements = 44;
        profile.source.concept_expressions = 20_000;
        profile.source.max_concept_depth = 2;
        profile.source.abox_axioms = 185;
        profile.source.class_assertions = 163;
        profile.source.role_assertions = 20;
        for (kind, count) in [
            ("SubClassOf", 8_250),
            ("SubObjectPropertyOf", 147),
            ("InverseObjectProperties", 42),
            ("ClassAssertion", 163),
            ("ObjectPropertyAssertion", 20),
            ("DifferentIndividuals", 2),
        ] {
            profile.source.axiom_types.insert(kind.into(), count);
        }

        // A conservative universal-role occurrence keeps the input on eager
        // nominal CB, the only nominal route that never consults the bridge.
        profile.expressivity.universal_role = true;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(!typed_object_abox_bridge_candidate(&profile));
        assert_eq!(select(&profile), Route::Nominals);

        // After the frontend elides a vacuous `R ⊑ owl:topObjectProperty`, the
        // profile describes a universal-role-free ontology: the exact typed
        // bridge portfolio is selected and retains its nominal-aware CB
        // fallback, on the ordinary low-latency schedule for compact ABoxes.
        profile.expressivity.universal_role = false;
        assert!(typed_object_abox_bridge_candidate(&profile));
        assert_eq!(select(&profile), Route::CertifiedNominals);
        assert!(certified_nominal_production_probe_candidate(&profile));
        assert!(!certified_nominal_general_ht_probe_candidate(&profile));
        assert!(!compact_typed_bridge_first_candidate(&profile));
        assert!(!sequential_typed_bridge_candidate(&profile));
        assert_eq!(
            automatic_atomic_fallback(Route::CertifiedNominals, &profile),
            None,
            "the portfolio carries its own exact nominal fallback"
        );
    }

    #[test]
    fn large_horn_functional_terminology_retains_exact_fallback() {
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
        assert_eq!(select(&profile), Route::ProductionAll);
        assert_eq!(production_bridge_subject_workers(&profile), Some("2"));

        // Production selects before clausification. The source-only profile
        // must therefore make the same decision as `km profile`, which fills
        // clause statistics after normalisation.
        let mut pre_clausification = profile.clone();
        pre_clausification.clauses = Default::default();
        assert_eq!(select(&pre_clausification), Route::ProductionAll);
        assert_eq!(
            production_bridge_subject_workers(&pre_clausification),
            Some("2")
        );

        profile.source.complements = 1;
        assert!(!large_horn_functional_native_bridge_candidate(&profile));
    }

    #[test]
    fn automatic_atomic_declines_retain_source_appropriate_fallbacks() {
        let mut nominal = OntologyProfile::default();
        nominal.source.abox_axioms = 1;
        assert_eq!(semantic_fragment(&nominal), SemanticFragment::Nominal);
        for route in [
            Route::Elc,
            Route::HtGeneral,
            Route::CertifiedCardNominals,
            Route::NominalNiTbox,
        ] {
            assert_eq!(
                automatic_atomic_fallback(route, &nominal),
                Some(Route::Nominals)
            );
        }

        let core = OntologyProfile::default();
        assert_eq!(semantic_fragment(&core), SemanticFragment::SriqCore);
        assert_eq!(
            automatic_atomic_fallback(Route::Elc, &core),
            Some(Route::ProductionAll)
        );
        assert_eq!(automatic_atomic_fallback(Route::CbPlain16, &core), None);

        let mut rules = OntologyProfile::default();
        rules.source.rule_axioms = 1;
        assert_eq!(automatic_atomic_fallback(Route::Elc, &rules), None);
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
        assert_eq!(certified_nominal_subject_workers(&profile), "4");
        let mut large = profile.clone();
        large.source.logical_axioms = 123_176;
        large.source.distinct_classes = 41_647;
        assert_eq!(certified_nominal_subject_workers(&large), "8");

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

    /// The smallest terminology of the measured context-parallel panel
    /// (`ore_ont_795`: 106,608 logical axioms, 47,144 classes, 10 object
    /// properties, 24,595 existential restrictions, 15.2 MiB of source).
    fn context_parallel_panel_profile() -> OntologyProfile {
        let mut profile = OntologyProfile::default();
        profile.expressivity.code = "SHI".into();
        profile.source.logical_axioms = 106_608;
        profile.source.tbox_axioms = 106_598;
        profile.source.rbox_axioms = 10;
        profile.source.declarations = 47_154;
        profile.source.declared_classes = 47_144;
        profile.source.declared_object_properties = 10;
        profile.source.distinct_classes = 47_144;
        profile.source.distinct_object_properties = 10;
        profile.source.subclass_axioms = 106_598;
        profile.source.role_inclusion_axioms = 10;
        profile.source.role_chain_axioms = 3;
        profile.source.intersections = 9_165;
        profile.source.existentials = 24_595;
        profile.source.bottom_occurrences = 2;
        profile.source.concept_expressions = 256_160;
        profile.source.max_concept_depth = 2;
        profile.source.max_concept_arity = 2;
        profile.source.file_bytes = 15_944_277;
        profile
            .source
            .axiom_types
            .insert("SubClassOf".into(), 106_598);
        profile
    }

    #[test]
    fn context_parallel_gate_arms_the_measured_el_terminology_family() {
        let profile = context_parallel_panel_profile();
        // The gate only ever schedules the bare EL route it was measured on.
        assert_eq!(select(&profile), Route::Elc);
        assert_eq!(elc_context_parallel_workers(&profile, 16), Some("8"));
        assert_eq!(elc_context_parallel_workers(&profile, 8), Some("8"));
        // Four workers improved every panel member as well; two did not, so a
        // machine that cannot supply four keeps the serial engine.
        assert_eq!(elc_context_parallel_workers(&profile, 7), Some("4"));
        assert_eq!(elc_context_parallel_workers(&profile, 4), Some("4"));
        assert_eq!(elc_context_parallel_workers(&profile, 3), None);
        assert_eq!(elc_context_parallel_workers(&profile, 2), None);
        assert_eq!(elc_context_parallel_workers(&profile, 1), None);
        assert_eq!(elc_context_parallel_workers(&profile, 0), None);
    }

    #[test]
    fn context_parallel_gate_arms_the_measured_wide_role_chain_free_family() {
        let mut profile = context_parallel_panel_profile();
        profile.source.logical_axioms = 175_170;
        profile.source.tbox_axioms = 175_147;
        profile.source.rbox_axioms = 23;
        profile.source.distinct_classes = 68_820;
        profile.source.declared_classes = 68_820;
        profile.source.existentials = 94_834;
        profile.source.distinct_object_properties = 29;
        profile.source.declared_object_properties = 29;
        profile.source.role_chain_axioms = 0;
        profile.source.file_bytes = 31_242_537;
        assert_eq!(select(&profile), Route::Elc);
        assert_eq!(elc_context_parallel_workers(&profile, 16), Some("8"));
        assert_eq!(elc_context_parallel_workers(&profile, 4), Some("4"));
        assert_eq!(elc_context_parallel_workers(&profile, 3), None);

        // Crossing each tight measured-band boundary fails closed instead of
        // admitting the unmeasured role-rich EL population.
        for mutate in [
            (|p: &mut OntologyProfile| p.source.logical_axioms = 149_999)
                as fn(&mut OntologyProfile),
            |p: &mut OntologyProfile| p.source.distinct_classes = 59_999,
            |p: &mut OntologyProfile| p.source.existentials = 89_999,
            |p: &mut OntologyProfile| p.source.distinct_object_properties = 19,
            |p: &mut OntologyProfile| p.source.role_chain_axioms = 1,
            |p: &mut OntologyProfile| p.source.file_bytes = 40 * 1024 * 1024 + 1,
        ] {
            let mut outside = profile.clone();
            mutate(&mut outside);
            assert_eq!(elc_context_parallel_workers(&outside, 16), None);
        }
    }

    #[test]
    fn context_parallel_gate_is_deterministic_for_one_profile() {
        let profile = context_parallel_panel_profile();
        let first = elc_context_parallel_workers(&profile, 16);
        for _ in 0..64 {
            assert_eq!(elc_context_parallel_workers(&profile, 16), first);
        }
        // The predicate reads the profile only; equal profiles decide equally.
        let copy = profile.clone();
        assert_eq!(copy, profile);
        assert_eq!(elc_context_parallel_workers(&copy, 16), first);
    }

    #[test]
    fn context_parallel_gate_declines_outside_the_measured_family() {
        // Individuals: the two ABox members of the panel hold its two largest
        // peak increases and neither recovers a gate.
        let mut abox = context_parallel_panel_profile();
        abox.source.abox_axioms = 1;
        abox.source.class_assertions = 1;
        abox.source.logical_axioms += 1;
        assert_eq!(elc_context_parallel_workers(&abox, 16), None);

        // Everything outside the EL class fragment the panel measured.
        for mutate in [
            (|p: &mut OntologyProfile| p.source.unions = 1) as fn(&mut OntologyProfile),
            |p: &mut OntologyProfile| p.source.complements = 1,
            |p: &mut OntologyProfile| p.source.universals = 1,
            |p: &mut OntologyProfile| p.source.min_cardinalities = 1,
            |p: &mut OntologyProfile| p.source.max_cardinalities = 1,
            |p: &mut OntologyProfile| p.source.exact_cardinalities = 1,
            |p: &mut OntologyProfile| p.source.qualified_cardinalities = 1,
            |p: &mut OntologyProfile| p.source.nominals = 1,
            |p: &mut OntologyProfile| p.source.has_values = 1,
            |p: &mut OntologyProfile| p.source.has_self = 1,
            |p: &mut OntologyProfile| p.source.datatype_constructors = 1,
            |p: &mut OntologyProfile| p.source.max_concept_depth = 4,
            |p: &mut OntologyProfile| p.source.imports = 1,
            |p: &mut OntologyProfile| p.source.rule_axioms = 1,
            |p: &mut OntologyProfile| p.source.unsupported_rule_axioms = 1,
        ] {
            let mut profile = context_parallel_panel_profile();
            mutate(&mut profile);
            assert_eq!(elc_context_parallel_workers(&profile, 16), None);
        }

        // Below the panel floors the saturation lap cannot repay the workers.
        let mut small = context_parallel_panel_profile();
        small.source.logical_axioms = 99_999;
        assert_eq!(elc_context_parallel_workers(&small, 16), None);
        let mut few_classes = context_parallel_panel_profile();
        few_classes.source.distinct_classes = 19_999;
        assert_eq!(elc_context_parallel_workers(&few_classes, 16), None);
        let mut few_existentials = context_parallel_panel_profile();
        few_existentials.source.existentials = 19_999;
        assert_eq!(elc_context_parallel_workers(&few_existentials, 16), None);

        // Above the panel ceilings the measured peak increase has no evidence.
        let mut large = context_parallel_panel_profile();
        large.source.logical_axioms = 400_001;
        assert_eq!(elc_context_parallel_workers(&large, 16), None);
        let mut wide_source = context_parallel_panel_profile();
        wide_source.source.file_bytes = 64 * 1024 * 1024 + 1;
        assert_eq!(elc_context_parallel_workers(&wide_source, 16), None);
        let mut role_sparse = context_parallel_panel_profile();
        role_sparse.source.distinct_object_properties = 7;
        assert_eq!(elc_context_parallel_workers(&role_sparse, 16), None);
        let mut role_rich = context_parallel_panel_profile();
        role_rich.source.distinct_object_properties = 13;
        assert_eq!(elc_context_parallel_workers(&role_rich, 16), None);
        let mut chain_rich = context_parallel_panel_profile();
        chain_rich.source.role_chain_axioms = 33;
        assert_eq!(elc_context_parallel_workers(&chain_rich, 16), None);
    }

    #[test]
    fn context_parallel_gate_carries_no_ontology_identity() {
        let source = include_str!("routing.rs");
        let start = source
            .find("pub(crate) fn elc_context_parallel_workers")
            .expect("the context-parallel gate is present");
        let body = &source[start..];
        let end = body.find("\n}\n").expect("the gate has a body");
        assert!(!body[..end].contains("ore_ont_"));
    }

    /// Projection ledger over the retained 592-ontology source profiles.
    ///
    /// `KM_ELC_CTX_PROFILE_DIR` points at the retained `*.owl.json` profile
    /// records; `KM_ELC_CTX_PROJECTION_OUT` optionally receives the ledger.
    /// Without the directory the test is inert, so the ordinary suite does not
    /// depend on corpus artifacts.
    #[test]
    fn context_parallel_projection_over_the_retained_profiles() {
        #[derive(serde::Deserialize)]
        struct Record {
            ont: String,
            profile: OntologyProfile,
        }

        let Some(dir) = std::env::var_os("KM_ELC_CTX_PROFILE_DIR") else {
            return;
        };
        let mut entries: Vec<std::path::PathBuf> = std::fs::read_dir(&dir)
            .expect("profile directory")
            .map(|entry| entry.expect("profile entry").path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "json"))
            .collect();
        entries.sort();
        let mut rows = vec![
            "ontology\troute\tarmed_workers\tlogical_axioms\tdistinct_classes\tobject_properties\texistentials\tfile_bytes".to_string(),
        ];
        let mut armed = 0usize;
        for path in &entries {
            let text = std::fs::read_to_string(path).expect("profile record");
            let record: Record = serde_json::from_str(&text).expect("profile record shape");
            let route = select(&record.profile);
            let workers = elc_context_parallel_workers(&record.profile, 16);
            // The schedule is armed only on the bare EL route, and only there.
            if workers.is_some() && route == Route::Elc {
                armed += 1;
            }
            if let Some(workers) = workers {
                assert_eq!(
                    route,
                    Route::Elc,
                    "{} armed {} workers off the bare EL route",
                    record.ont,
                    workers
                );
            }
            let source = &record.profile.source;
            rows.push(format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                record.ont,
                route.as_str(),
                workers.unwrap_or("serial"),
                source.logical_axioms,
                source.distinct_classes,
                source.distinct_object_properties,
                source.existentials,
                source.file_bytes,
            ));
        }
        assert_eq!(entries.len(), 592, "the retained corpus has 592 profiles");
        assert_eq!(
            armed, 10,
            "the retained projection must arm exactly the ten measured profiles"
        );
        if let Some(out) = std::env::var_os("KM_ELC_CTX_PROJECTION_OUT") {
            std::fs::write(out, rows.join("\n") + "\n").expect("ledger written");
        }
    }
}
