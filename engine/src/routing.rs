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
    Nominals,
    SeqOn,
    SeqOff,
}

impl Route {
    pub const NAMED: [Route; 36] = [
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
        SemanticFragment::Nominal if profile.inverse_cardinality_role_separable => {
            Route::CertifiedCardNominals
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
        // An ABox that fails the materialization certificate stays on the exact
        // nominal calculus. `certified_card_proxy_abox` can classify several of
        // these terminologies (ore_ont_7499 gold-exact) but it DROPS the ABox,
        // and dropping is only an under-approximation: it proves soundness, not
        // completeness. Completeness would additionally need ABox/TBox taxonomy
        // separability AND a complete consistency decision, because an
        // inconsistent KB entails every subsumption while a dropped ABox yields
        // an ordinary taxonomy. The frontend's `abox_inconsistent` precheck is
        // sound-only — it closes asserted memberships over named subclasses,
        // domain/range and SameIndividual and fires on an ASSERTED disjoint
        // pair, so `A ⊑ ⊥` with `ClassAssertion(A a)`, a cardinality clash, or a
        // role-chain-derived range clash all escape it. Until such a
        // certificate exists the route stays explicitly selectable only.
        SemanticFragment::Nominal => Route::Nominals,
        // A scoped inverse+cardinality ontology whose number-role component is
        // source-certified disjoint from inverse/non-simple roles must retain a
        // production route carrying the card arm. The worker independently
        // rechecks the normalized RBox before admitting that arm; all inverse
        // axioms remain live. Nominal inputs stay on the exact nominal fallback
        // here until the combined certified-nominals portfolio is installed.
        SemanticFragment::PositiveAbox | SemanticFragment::SriqCore
            if profile.inverse_cardinality_role_separable =>
        {
            Route::ProductionAll
        }
        SemanticFragment::PositiveAbox | SemanticFragment::SriqCore => {
            let learned = routing_tree_generated::select(profile);
            if sriq_policy_eligible(learned) {
                learned
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
/// MEASUREMENT-ONLY cardinality race for a scoped inverse+cardinality ontology
/// whose ABox cannot be materialized natively (`card_number_role_separable`
/// holds, `inverse_cardinality_role_separable` does not). Never selected
/// automatically; see the fail-closed branch in [`select`].
///
/// The source certificate proves no number restriction touches an inverse,
/// non-simple, universal or clause-retained-constraint role, so the fast Ht's
/// first-class `≥n`/`≤n` rules with inverse-aware blocking decide the TBox, and
/// `KM_HT_CARD_PROXY_ABOX` keeps the uncertified native ABox out of the card
/// input (seeding it costs the whole classification and still cannot
/// materialize chain-derived edges).
///
/// **Contract: sound, NOT complete for the ontology as a whole.** Dropping ABox
/// axioms only removes constraints, so every published subsumption is entailed.
/// Completeness needs two further proofs this route does not have: that the
/// ABox cannot change a named-class subsumption (nominal-free TBox, no
/// universal role — `positive_abox_tbox_separable` is the existing certificate
/// of that shape), and that the KB is CONSISTENT, since an inconsistent KB
/// entails every subsumption while a dropped ABox still yields an ordinary
/// taxonomy. `abox_inconsistent` decides only asserted-disjointness and
/// negative-assertion clashes, so a derived contradiction (`A ⊑ ⊥` with
/// `ClassAssertion(A a)`, a cardinality clash, a role-chain-derived range
/// clash) is missed. Callers select this route when they have established
/// consistency and ABox irrelevance by other means.
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
    "KM_NO_HT_RACE",
    "KM_NO_HT_QO_ROUTER",
    "KM_NO_HT_SHOQ",
    "KM_NO_HT_CARD",
    "KM_NO_HT_RULES",
    "KM_HT_MODE",
    "KM_HT_ONLY",
    "KM_HT_BRIDGE",
    "KM_HT_BRIDGE_ONLY",
    "KM_HT_FORCE",
    "KM_HT_QO",
    "KM_HT_QO_PC",
    "KM_HT_QO_INVCOMPOSE",
    "KM_HT_QO_FPROP",
    "KM_HT_QO_SAT",
    "KM_HT_QO_KPSET",
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
    "KM_SEQ_ORDER",
    "KM_NO_SEQ_ORDER",
];

#[cfg(test)]
mod tests {
    use super::*;

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
        ] {
            assert!(
                Route::CertifiedCardProxyAbox.settings().contains(&required),
                "certified_card_proxy_abox must carry {required:?}"
            );
        }
        for forbidden in ["KM_NO_HT_CARD", "KM_NO_HT_RACE", "KM_NOMINALS"] {
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
        // The number-role half ALONE (ore_ont_7499: its asserted edges feed a
        // proper role chain, so the native ABox cannot be materialized) must
        // NOT pick up the ABox-dropping cardinality race. That route is sound
        // but not complete for the whole ontology, so it stays explicit-only
        // and the exact nominal calculus keeps the input.
        profile.inverse_cardinality_role_separable = false;
        assert_eq!(
            select(&profile),
            Route::Nominals,
            "an unmaterializable ABox must keep the exact nominal calculus"
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
        assert!(!independent_large_abox_candidate(&profile));
        assert_eq!(select(&profile), Route::Nominals);
        profile.source.role_assertions = 0;

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
    fn large_nominal_abox_uses_bounded_exact_portfolio() {
        let mut profile = OntologyProfile::default();
        profile.source.abox_axioms = 256_427;
        profile.source.class_assertions = 111_561;
        profile.source.role_assertions = 78_441;
        profile.source.distinct_individuals = 129_647;
        profile.expressivity.nominal_individual = true;
        profile.expressivity.nominal = true;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert!(large_nominal_portfolio_candidate(&profile));
        assert_eq!(select(&profile), Route::CertifiedNominals);

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

    /// The ABox-dropping cardinality race must never be reachable from the
    /// automatic policy, whatever the profile says. Dropping an ABox is an
    /// under-approximation: it keeps every published subsumption entailed, but
    /// an inconsistent KB entails EVERY subsumption, and neither the source
    /// profile nor the frontend precheck decides consistency.
    #[test]
    fn the_abox_dropping_card_race_is_never_selected_automatically() {
        let mut profile = OntologyProfile::default();
        profile.card_number_role_separable = true;
        for abox_axioms in [0, 1, 223] {
            for separable in [false, true] {
                for positive in [false, true] {
                    profile.source.abox_axioms = abox_axioms;
                    profile.inverse_cardinality_role_separable = separable;
                    profile.positive_abox_tbox_separable = positive;
                    assert_ne!(
                        select(&profile),
                        Route::CertifiedCardProxyAbox,
                        "abox={abox_axioms} separable={separable} positive={positive}"
                    );
                }
            }
        }
        // It stays reachable by explicit request, which is how the ore_ont_7499
        // result is reproduced.
        assert_eq!(
            "certified_card_proxy_abox".parse::<Route>().unwrap(),
            Route::CertifiedCardProxyAbox
        );
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
