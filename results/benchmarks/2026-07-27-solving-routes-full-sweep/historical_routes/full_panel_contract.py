#!/usr/bin/env python3
"""Source-bound historical KM routes omitted from the initial sweep."""

KM_REVISION = "mixed-source-bound-historical"
KONCLUDE_REVISION = "not-in-supplement"
RUSTDL_REVISION = "not-in-supplement"
SEQUOIA_REVISION = "not-in-supplement"


def panel() -> list[dict]:
    rows = [
        {
            "arm": "km_historical_3215_kpset_barrier",
            "family": "km_documented_solution_route",
            "kind": "km",
            "binary_key": "historical-3215",
            "source_revision": "2026-07-13-kpset-closure",
            "documented_route": "kpset_barrier",
            "environment": [
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
            "args": [],
            "standard_summary": False,
        },
        {
            "arm": "km_historical_7499_card_race",
            "family": "km_documented_solution_route",
            "kind": "km",
            "binary_key": "historical-7499",
            "source_revision": "git:0d20dd13312c16dec4ff256852979fb4c927556a",
            "documented_route": "card_race",
            "environment": [
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
            "args": [],
            "standard_summary": False,
        },
    ]
    assert len({row["arm"] for row in rows}) == 2
    return rows
