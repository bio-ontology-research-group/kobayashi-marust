#!/usr/bin/env python3
"""Six-arm ORE panel for the three KM policies and external references."""

from __future__ import annotations

import json


KM_REVISION = "847a872a13e0d617c950ff5121d44ac89632b174"
KONCLUDE_REVISION = "0002e80635403960a7df5d93bd0e8f994d4952d0"


def panel() -> list[dict]:
    rows = [
        {
            "arm": f"km_route_{route.replace('-', '_')}",
            "family": "km_policy",
            "kind": "km",
            "binary_key": "main",
            "source_revision": KM_REVISION,
            "route": route,
            "args": [],
            "standard_summary": True,
        }
        for route in ("auto", "auto-speed", "auto-memory")
    ]
    rows.extend(
        [
            {
                "arm": "elk",
                "family": "baseline",
                "kind": "elk",
                "source_revision": "ELK-0.6.0",
                "java_heap": "-Xmx28g",
                "standard_summary": True,
            },
            {
                "arm": "hermit",
                "family": "baseline",
                "kind": "hermit",
                "source_revision": "HermiT-1.4.6.519-SNAPSHOT",
                "java_heap": "-Xmx28g",
                "standard_summary": True,
            },
            {
                "arm": "konclude",
                "family": "baseline",
                "kind": "konclude",
                "source_revision": KONCLUDE_REVISION,
                "workers": 16,
                "standard_summary": True,
            },
        ]
    )
    assert len(rows) == 6
    assert len({row["arm"] for row in rows}) == 6
    return rows


if __name__ == "__main__":
    for procedure in panel():
        print(json.dumps(procedure, sort_keys=True))
