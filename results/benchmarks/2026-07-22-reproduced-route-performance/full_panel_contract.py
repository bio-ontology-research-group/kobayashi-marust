#!/usr/bin/env python3
"""Frozen procedure contract for the 2026-07-22 all-options ORE sweep.

Every Slurm array task owns one ontology and executes this ordered panel.  KM
"configuration option" means every public value printed by ``km routes``.  It
does not mean the unbounded Cartesian product of numeric budgets, internal
worker controls, diagnostics, profilers, or output-format settings.
"""

from __future__ import annotations

import json


KM_REVISION = "8c731f43b3c8a277f5fd7a25687e35afb4c4045e"
KONCLUDE_REVISION = "0002e80635403960a7df5d93bd0e8f994d4952d0"
RUSTDL_REVISION = "8c2bb1bf43d936e56d77ae439c04d2feb3f6ebf5"
SEQUOIA_REVISION = "c5248ec7be302efc850cf07ab30a0ea651db81b6"


KM_ROUTES = (
    "auto",
    "manual",
    "default",
    "default8",
    "default1",
    "production_all",
    "production_all8",
    "production_all1",
    "cb_plain16",
    "cb_plain8",
    "cb_plain1",
    "cb_absorb16",
    "cb_absorb8",
    "cb_absorb1",
    "cb_trigger16",
    "cb_trigger8",
    "cb_trigger1",
    "cb_absorb_portfolio16",
    "elc",
    "elc_cert",
    "lean",
    "ht_general",
    "ht_qo",
    "ht_shoq",
    "ht_card",
    "ht_bridge",
    "ht_features",
    "ht_full",
    "ht_rules",
    "tableau",
    "tab_race",
    "card_fn",
    "nominals",
    "seq_on",
    "seq_off",
)

# Chronological source snapshots make the whole July optimization stack
# reproducible even where later edits prevent a clean one-factor reverse patch.
# These rows are explicitly "stages", not causal one-factor estimates.
OPTIMIZATION_STAGES = (
    ("km_opt_stage_pre", "17c0c7581278d4b355efa04e9444e03b87cba9ab"),
    ("km_opt_stage_result_extract", "757c073f3a8a29ffdeb1403f9bbf4f0fe43326f9"),
    ("km_opt_stage_inline_subst", "536ca58b32bf20ae2d24426dae74f6d1b399d2fc"),
    ("km_opt_stage_role_reach", "0883fe5b65ce8743ea711f76e77ec434ff4b1865"),
    ("km_opt_stage_rsucc_edge", "3fd3b77e52700b530b3f1ade11b945ffb9afdbfb"),
    ("km_opt_stage_rollback", "794f6c21282b38f9e2e28523c66496e7fa7c84a1"),
    ("km_opt_stage_oneway_subsume", "3d1926a9f987ed0939c3282047b753e97afa8b44"),
    ("km_opt_stage_crossscan_gate", "a639ab59bfb20b04f0131a2b7b7cb727117a936b"),
    ("km_opt_stage_clause_hash_reuse", "55222f1704cb48341e91e2571dd039646074fbd4"),
    ("km_opt_stage_core_hash_intern", "61b35c0f82ed07b29d9c117d492a03154866af69"),
    ("km_opt_stage_backsub_unindex", "8407ce2caa17ffcf64d46aed308ede6903de1c80"),
)

# These reverse cleanly against the frozen main source.  They are true
# one-factor ablations: current main minus exactly the named commit.
OPTIMIZATION_ABLATIONS = (
    ("km_opt_ablate_result_extract", "757c073f3a8a29ffdeb1403f9bbf4f0fe43326f9"),
    ("km_opt_ablate_oneway_subsume", "3d1926a9f987ed0939c3282047b753e97afa8b44"),
    ("km_opt_ablate_clause_hash_reuse", "55222f1704cb48341e91e2571dd039646074fbd4"),
    ("km_opt_ablate_core_hash_intern", "61b35c0f82ed07b29d9c117d492a03154866af69"),
    ("km_opt_ablate_backsub_unindex", "8407ce2caa17ffcf64d46aed308ede6903de1c80"),
)

# Exact environments cited by at least one accepted row in the 589-route
# ledger, where the environment is not already identical to a single public
# named route.  These are replayed over the entire corpus, not just their
# historically selected ontology.
DOCUMENTED_SOLUTION_ROUTES = (
    (
        "km_solution_card_race",
        "card_race",
        [
            "KM_ROUTE=manual",
            "KM_THREADS=16",
            "KM_PAR_MEM_GB=18",
            "KM_HT_MEM_GB=18",
            "KM_KEEP_CHAIN_AXIOMS=1",
            "KM_HT_MODE=race",
            "KM_NO_HT_QO_ROUTER=1",
            "KM_NO_HT_SHOQ=1",
            "KM_NO_ELC_PORTFOLIO=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
        ],
    ),
    (
        "km_solution_htforce_race",
        "htforce_race",
        [
            "KM_ROUTE=manual",
            "KM_THREADS=16",
            "KM_PAR_MEM_GB=18",
            "KM_HT_MEM_GB=18",
            "KM_KEEP_CHAIN_AXIOMS=1",
            "KM_ABSORB=1",
            "KM_ABSORB_PORTFOLIO=1",
            "KM_HT_FORCE=1",
            "KM_HT_MODE=race",
        ],
    ),
    (
        "km_solution_kpset_barrier",
        "kpset_barrier",
        [
            "KM_ROUTE=manual",
            "KM_TRIGGER_ABSORB=1",
            "KM_KEEP_CHAIN_AXIOMS=1",
            "KM_BRIDGE_PROBE_BUDGET_S=30",
            "KM_BRIDGE_RETRY_ROUNDS=0",
            "KM_HT_SATURATION_BUDGET_S=180",
            "KM_HT_MEM_GB=18",
            "KM_PAR_MEM_GB=18",
            "KM_THREADS=16",
        ],
    ),
    (
        "km_solution_legacy_tab_race",
        "legacy_tab_race",
        [
            "KM_ROUTE=manual",
            "KM_THREADS=16",
            "KM_PAR_MEM_GB=18",
            "KM_HT_MEM_GB=18",
            "KM_KEEP_CHAIN_AXIOMS=1",
            "KM_TAB_RACE=1",
            "KM_TAB_FEAT=1",
            "KM_TAB_RACE_DELAY=0",
            "KM_NO_HT_RACE=1",
            "KM_NO_ELC_PORTFOLIO=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
        ],
    ),
    (
        "km_solution_nomlink_default",
        "nomlink_default",
        [
            "KM_ROUTE=manual",
            "KM_THREADS=16",
            "KM_PAR_MEM_GB=18",
            "KM_HT_MEM_GB=18",
            "KM_KEEP_CHAIN_AXIOMS=1",
        ],
    ),
    (
        "km_solution_shoq_race",
        "shoq_race",
        [
            "KM_ROUTE=manual",
            "KM_THREADS=16",
            "KM_PAR_MEM_GB=18",
            "KM_HT_MEM_GB=18",
            "KM_KEEP_CHAIN_AXIOMS=1",
            "KM_HT_MODE=race",
            "KM_NO_HT_QO_ROUTER=1",
            "KM_NO_HT_CARD=1",
            "KM_NO_ELC_PORTFOLIO=1",
            "KM_NO_ABSORB_PORTFOLIO=1",
            "KM_ABSORB=0",
        ],
    ),
    (
        "km_solution_ht_rules_manual",
        "ht_rules",
        ["KM_ROUTE=manual", "KM_HT_RULES=1"],
    ),
    (
        "km_solution_production_all_explicit",
        "production_all",
        [
            "KM_ROUTE=production_all",
            "KM_THREADS=16",
            "KM_PAR_MEM_GB=18",
            "KM_TRIGGER_ABSORB=1",
            "KM_BRIDGE_PROBE_BUDGET_S=30",
            "KM_BRIDGE_RETRY_ROUNDS=0",
            "KM_HT_SATURATION_BUDGET_S=180",
        ],
    ),
)

BASELINES = (
    {
        "arm": "konclude",
        "family": "baseline",
        "kind": "konclude",
        "source_revision": KONCLUDE_REVISION,
        "standard_summary": True,
    },
    {
        "arm": "hermit",
        "family": "baseline",
        "kind": "hermit",
        "source_revision": "HermiT-1.4.6.519-SNAPSHOT",
        "standard_summary": True,
    },
    {
        "arm": "elk",
        "family": "baseline",
        "kind": "elk",
        "source_revision": "ELK-0.6.0",
        "standard_summary": True,
    },
    {
        "arm": "rustdl_complete",
        "family": "baseline",
        "kind": "rustdl",
        "source_revision": RUSTDL_REVISION,
        "args": ["--pair-timeout-ms", "0", "--global-timeout-ms", "0"],
        "standard_summary": True,
    },
    {
        "arm": "rustdl_default",
        "family": "baseline_variant",
        "kind": "rustdl",
        "source_revision": RUSTDL_REVISION,
        "args": [],
        "standard_summary": False,
    },
    {
        "arm": "sequoia_strict",
        "family": "baseline",
        "kind": "sequoia",
        "source_revision": SEQUOIA_REVISION,
        "args": [],
        "standard_summary": True,
    },
    {
        "arm": "sequoia_ignore_unsupported",
        "family": "baseline_variant",
        "kind": "sequoia",
        "source_revision": SEQUOIA_REVISION,
        "args": ["--ignoreUnsupportedFeatures"],
        "standard_summary": False,
    },
)


def panel() -> list[dict]:
    rows: list[dict] = []
    for route in KM_ROUTES:
        rows.append(
            {
                "arm": f"km_route_{route}",
                "family": "km_route",
                "kind": "km",
                "binary_key": "main",
                "source_revision": KM_REVISION,
                "route": route,
                "args": [],
                "standard_summary": route == "auto",
            }
        )
    for arm, revision in OPTIMIZATION_STAGES:
        rows.append(
            {
                "arm": arm,
                "family": "km_optimization_stage",
                "kind": "km",
                "binary_key": f"stage-{revision[:12]}",
                "source_revision": revision,
                "route": "production_all",
                "args": [],
                "standard_summary": False,
            }
        )
    for arm, reverted_revision in OPTIMIZATION_ABLATIONS:
        rows.append(
            {
                "arm": arm,
                "family": "km_optimization_ablation",
                "kind": "km",
                "binary_key": f"ablate-{reverted_revision[:12]}",
                "source_revision": KM_REVISION,
                "reverted_revision": reverted_revision,
                "route": "production_all",
                "args": [],
                "standard_summary": False,
            }
        )
    for arm, documented_route, environment in DOCUMENTED_SOLUTION_ROUTES:
        rows.append(
            {
                "arm": arm,
                "family": "km_documented_solution_route",
                "kind": "km",
                "binary_key": "main",
                "source_revision": KM_REVISION,
                "documented_route": documented_route,
                "environment": environment,
                "args": [],
                "standard_summary": False,
            }
        )
    rows.extend(dict(row) for row in BASELINES)
    assert len(rows) == 66
    assert len({row["arm"] for row in rows}) == len(rows)
    return rows


if __name__ == "__main__":
    for procedure in panel():
        print(json.dumps(procedure, sort_keys=True))
