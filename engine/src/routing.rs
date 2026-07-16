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
    pub const NAMED: [Route; 33] = [
        Route::Default,
        Route::Default8,
        Route::Default1,
        Route::ProductionAll,
        Route::ProductionAll8,
        Route::ProductionAll1,
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
            Route::CbPlain16
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
    /// A positive ABox whose consistency and TBox-separation follow from the
    /// source certificate. It may use the same complete TBox mechanisms as the
    /// nominal-free core; all other ABoxes remain `Nominal`.
    PositiveAbox,
    Nominal,
    SriqCore,
}

pub fn semantic_fragment(profile: &OntologyProfile) -> SemanticFragment {
    if profile.source.unsupported_rule_axioms > 0 {
        SemanticFragment::UnsupportedRules
    } else if profile.source.rule_axioms > 0 {
        SemanticFragment::Rules
    } else if profile.source.abox_axioms > 0 && profile.positive_abox_tbox_separable {
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
        SemanticFragment::Nominal => Route::Nominals,
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

const PRODUCTION_ALL: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_HT_ONLY", "certified"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
    ("KM_BRIDGE_RETRY_ROUNDS", "0"),
    ("KM_HT_SATURATION_BUDGET_S", "180"),
];
const PRODUCTION_ALL_8: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_HT_ONLY", "certified"),
    ("KM_THREADS", "8"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
    ("KM_BRIDGE_RETRY_ROUNDS", "0"),
    ("KM_HT_SATURATION_BUDGET_S", "180"),
];
const PRODUCTION_ALL_1: &[(&str, &str)] = &[
    ("KM_MECHANISM", "portfolio"),
    ("KM_HT_ONLY", "certified"),
    ("KM_THREADS", "1"),
    ("KM_TRIGGER_ABSORB", "1"),
    ("KM_BRIDGE_PROBE_BUDGET_S", "30"),
    ("KM_BRIDGE_RETRY_ROUNDS", "0"),
    ("KM_HT_SATURATION_BUDGET_S", "180"),
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
    "KM_SEQ_ORDER",
    "KM_NO_SEQ_ORDER",
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_matrix_route_round_trips() {
        for route in Route::NAMED {
            assert_eq!(route.as_str().parse::<Route>().unwrap(), route);
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
            Route::CbAbsorbPortfolio16,
            Route::TabRace,
        ] {
            assert!(!route.is_atomic(), "{} must remain manual-only", route);
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
    }

    #[test]
    fn semantic_fragment_gate_precedes_the_learned_tree() {
        let mut profile = OntologyProfile::default();
        assert_eq!(semantic_fragment(&profile), SemanticFragment::SriqCore);
        assert_eq!(select(&profile), Route::CbPlain16);

        profile.source.abox_axioms = 1;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::Nominal);
        assert_eq!(select(&profile), Route::Nominals);

        profile.schema_version = 2;
        profile.positive_abox_tbox_separable = true;
        assert_eq!(semantic_fragment(&profile), SemanticFragment::PositiveAbox);
        assert_eq!(select(&profile), Route::CbPlain16);

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
            Route::HtFeatures,
            Route::HtFull,
            Route::CardFn,
            Route::Nominals,
            Route::HtRules,
        ] {
            assert!(!sriq_policy_eligible(route), "{route} must not pass");
        }
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
