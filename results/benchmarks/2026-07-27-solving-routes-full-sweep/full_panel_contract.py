#!/usr/bin/env python3
"""Frozen 2026-07-27 contract: every historically successful KM route."""

from __future__ import annotations

import json

KM_REVISION = "23601068839bfb8f6c9cc7efae851de125b584ac"
KONCLUDE_REVISION = "0002e80635403960a7df5d93bd0e8f994d4952d0"
RUSTDL_REVISION = "not-in-panel"
SEQUOIA_REVISION = "not-in-panel"

KM_ROUTES = (
    "auto", "manual", "default", "default8", "default1",
    "production_all", "production_all8", "production_all1",
    "cb_plain16", "cb_plain8", "cb_plain1",
    "cb_absorb16", "cb_absorb8", "cb_absorb1",
    "cb_trigger16", "cb_trigger8", "cb_trigger1",
    "cb_absorb_portfolio16", "elc", "elc_cert", "lean",
    "ht_general", "ht_qo", "ht_shoq", "ht_card", "ht_bridge",
    "ht_features", "ht_full", "ht_rules", "tableau", "tab_race",
    "card_fn", "nominals", "seq_on", "seq_off",
)

DOCUMENTED_SOLUTION_ROUTES = (
    ("km_solution_card_race", "card_race", [
        "KM_ROUTE=manual", "KM_THREADS=16", "KM_PAR_MEM_GB=18",
        "KM_HT_MEM_GB=18", "KM_KEEP_CHAIN_AXIOMS=1", "KM_HT_MODE=race",
        "KM_NO_HT_QO_ROUTER=1", "KM_NO_HT_SHOQ=1",
        "KM_NO_ELC_PORTFOLIO=1", "KM_NO_ABSORB_PORTFOLIO=1", "KM_ABSORB=0",
    ]),
    ("km_solution_htforce_race", "htforce_race", [
        "KM_ROUTE=manual", "KM_THREADS=16", "KM_PAR_MEM_GB=18",
        "KM_HT_MEM_GB=18", "KM_KEEP_CHAIN_AXIOMS=1", "KM_ABSORB=1",
        "KM_ABSORB_PORTFOLIO=1", "KM_HT_FORCE=1", "KM_HT_MODE=race",
    ]),
    ("km_solution_kpset_barrier", "kpset_barrier", [
        "KM_ROUTE=manual", "KM_TRIGGER_ABSORB=1", "KM_KEEP_CHAIN_AXIOMS=1",
        "KM_BRIDGE_PROBE_BUDGET_S=30", "KM_BRIDGE_RETRY_ROUNDS=0",
        "KM_HT_SATURATION_BUDGET_S=180", "KM_HT_MEM_GB=18",
        "KM_PAR_MEM_GB=18", "KM_THREADS=16",
    ]),
    ("km_solution_legacy_tab_race", "legacy_tab_race", [
        "KM_ROUTE=manual", "KM_THREADS=16", "KM_PAR_MEM_GB=18",
        "KM_HT_MEM_GB=18", "KM_KEEP_CHAIN_AXIOMS=1", "KM_TAB_RACE=1",
        "KM_TAB_FEAT=1", "KM_TAB_RACE_DELAY=0", "KM_NO_HT_RACE=1",
        "KM_NO_ELC_PORTFOLIO=1", "KM_NO_ABSORB_PORTFOLIO=1", "KM_ABSORB=0",
    ]),
    ("km_solution_nomlink_default", "nomlink_default", [
        "KM_ROUTE=manual", "KM_THREADS=16", "KM_PAR_MEM_GB=18",
        "KM_HT_MEM_GB=18", "KM_KEEP_CHAIN_AXIOMS=1",
    ]),
    ("km_solution_shoq_race", "shoq_race", [
        "KM_ROUTE=manual", "KM_THREADS=16", "KM_PAR_MEM_GB=18",
        "KM_HT_MEM_GB=18", "KM_KEEP_CHAIN_AXIOMS=1", "KM_HT_MODE=race",
        "KM_NO_HT_QO_ROUTER=1", "KM_NO_HT_CARD=1",
        "KM_NO_ELC_PORTFOLIO=1", "KM_NO_ABSORB_PORTFOLIO=1", "KM_ABSORB=0",
    ]),
    ("km_solution_ht_rules_manual", "ht_rules", [
        "KM_ROUTE=manual", "KM_HT_RULES=1",
    ]),
    ("km_solution_production_all_explicit", "production_all", [
        "KM_ROUTE=production_all", "KM_THREADS=16", "KM_PAR_MEM_GB=18",
        "KM_TRIGGER_ABSORB=1", "KM_BRIDGE_PROBE_BUDGET_S=30",
        "KM_BRIDGE_RETRY_ROUNDS=0", "KM_HT_SATURATION_BUDGET_S=180",
    ]),
    ("km_solution_9540_exact_full_completion", "9540_exact_full_completion", [
        "KM_ROUTE=manual", "KM_TIMING=1", "KM_THREADS=16",
        "KM_PAR_MEM_GB=18", "KM_HT_MEM_GB=18", "KM_MECHANISM=ht",
        "KM_NO_ELC=1", "KM_NO_HT_RULES=1", "KM_NO_ABSORB_PORTFOLIO=1",
        "KM_ABSORB=0", "KM_NO_HT_QO_ROUTER=1", "KM_NO_HT_SHOQ=1",
        "KM_NO_HT_CARD=1", "KM_TRIGGER_ABSORB=1",
        "KM_BRIDGE_PROBE_BUDGET_S=220", "KM_BRIDGE_RETRY_ROUNDS=0",
        "KM_HT_SATURATION_BUDGET_S=180", "KM_HT_ONLY=bridge",
        "KM_NOMINALS=1", "KM_KEEP_CHAIN_AXIOMS=1", "KM_HT_NICE=0",
        "RUST_BACKTRACE=1",
    ]),
)

BASELINES = (
    {"arm": "konclude", "family": "baseline", "kind": "konclude",
     "source_revision": KONCLUDE_REVISION, "standard_summary": True},
    {"arm": "hermit", "family": "baseline", "kind": "hermit",
     "source_revision": "HermiT-1.4.6.519-SNAPSHOT", "standard_summary": True},
    {"arm": "elk", "family": "baseline", "kind": "elk",
     "source_revision": "ELK-0.6.0", "standard_summary": True},
)


def panel() -> list[dict]:
    rows = [
        {"arm": f"km_route_{route}", "family": "km_route", "kind": "km",
         "binary_key": "main", "source_revision": KM_REVISION, "route": route,
         "args": [], "standard_summary": route == "auto"}
        for route in KM_ROUTES
    ]
    rows.extend(
        {"arm": arm, "family": "km_documented_solution_route", "kind": "km",
         "binary_key": "main", "source_revision": KM_REVISION,
         "documented_route": documented_route, "environment": environment,
         "args": [], "standard_summary": False}
        for arm, documented_route, environment in DOCUMENTED_SOLUTION_ROUTES
    )
    rows.extend(dict(row) for row in BASELINES)
    assert len(rows) == 47
    assert len({row["arm"] for row in rows}) == len(rows)
    return rows


if __name__ == "__main__":
    for procedure in panel():
        print(json.dumps(procedure, sort_keys=True))
