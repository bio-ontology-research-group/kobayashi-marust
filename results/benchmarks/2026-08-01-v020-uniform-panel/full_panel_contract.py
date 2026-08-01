#!/usr/bin/env python3
"""Current-release ORE panel: all KM routes plus pinned comparison modes."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path


KM_REVISION = "364b8b2ebe99ea06e8e722e5c5613422267d9ac5"

# Reuse only the externally versioned baseline definitions and the exact
# documented environment bundles from the hash-bound 2026-07-22 contract.
# Optimization stages and ablations are deliberately not current routes.
_source = Path(__file__).with_name("_frozen_contract_20260722.py")
_spec = importlib.util.spec_from_file_location("frozen_contract_20260722", _source)
if _spec is None or _spec.loader is None:
    raise RuntimeError(f"cannot load frozen contract source: {_source}")
_frozen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_frozen)

DOCUMENTED_SOLUTION_ROUTES = _frozen.DOCUMENTED_SOLUTION_ROUTES
BASELINES = _frozen.BASELINES

KM_ROUTES = (
    "auto",
    "manual",
    "default",
    "default8",
    "default1",
    "production_all",
    "production_all8",
    "production_all1",
    "certified_card_nominals",
    "certified_card_proxy_abox",
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
    "certified_nominals",
    "ht_features",
    "ht_full",
    "ht_rules",
    "tableau",
    "tab_race",
    "card_fn",
    "nominal_ni_tbox",
    "nominal_ni_abox",
    "nominals",
    "seq_on",
    "seq_off",
)


def panel() -> list[dict]:
    rows = [
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
        for route in KM_ROUTES
    ]
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
    assert len(KM_ROUTES) == 40
    assert len(DOCUMENTED_SOLUTION_ROUTES) == 8
    assert len(BASELINES) == 7
    assert len(rows) == 55
    assert len({row["arm"] for row in rows}) == len(rows)
    return rows


if __name__ == "__main__":
    for procedure in panel():
        print(json.dumps(procedure, sort_keys=True))
