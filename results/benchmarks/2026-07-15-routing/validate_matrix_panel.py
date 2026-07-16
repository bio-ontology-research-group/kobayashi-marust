#!/usr/bin/env python3
"""Reject partial, duplicated, or provenance-inconsistent ontology panels."""

import argparse
import json

from matrix_contract import ALL_ARMS, KM_ARMS, NO_KONCLUDE_GOLD


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("panel")
    parser.add_argument("--ontology", required=True)
    args = parser.parse_args()
    rows = []
    with open(args.panel, encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            try:
                rows.append(json.loads(line))
            except ValueError as error:
                raise SystemExit(f"line {line_number}: invalid JSON: {error}")
    arms = [row.get("arm") for row in rows]
    if len(rows) != len(ALL_ARMS) or set(arms) != set(ALL_ARMS):
        missing = sorted(set(ALL_ARMS) - set(arms))
        duplicates = sorted({arm for arm in arms if arms.count(arm) > 1})
        unexpected = sorted(set(arms) - set(ALL_ARMS))
        raise SystemExit(
            f"bad panel rows={len(rows)} missing={missing} "
            f"duplicates={duplicates} unexpected={unexpected}"
        )
    if any(row.get("ont") != args.ontology for row in rows):
        raise SystemExit("panel contains a row for another ontology")
    order = sorted(row.get("order_index") for row in rows)
    if order != list(range(len(ALL_ARMS))):
        raise SystemExit(f"bad rotated order indices: {order}")
    hosts = {row.get("host") for row in rows}
    if len(hosts) != 1 or None in hosts:
        raise SystemExit(f"panel did not run on one identified host: {hosts}")
    runner_hashes = {row.get("runner_sha256") for row in rows}
    if len(runner_hashes) != 1 or None in runner_hashes:
        raise SystemExit(f"panel used missing or mixed runner hashes: {runner_hashes}")
    for row in rows:
        arm = row["arm"]
        if arm in KM_ARMS and row.get("requested_route") != arm:
            raise SystemExit(
                f"route provenance mismatch for {arm}: {row.get('requested_route')!r}"
            )
        if arm not in KM_ARMS and row.get("requested_route") is not None:
            raise SystemExit(f"baseline {arm} inherited KM_ROUTE")

    expected_gold_kind = (
        "none" if args.ontology in NO_KONCLUDE_GOLD else "konclude"
    )
    gold_kinds = {row.get("gold_kind") for row in rows}
    if gold_kinds != {expected_gold_kind}:
        raise SystemExit(
            f"gold-kind mismatch: expected {expected_gold_kind}, observed {gold_kinds}"
        )
    gold_names = {row.get("gold_basename") for row in rows}
    gold_hashes = {row.get("gold_sha256") for row in rows}
    if expected_gold_kind == "konclude":
        expected_name = f"konclude__{args.ontology}.sig.gz"
        if gold_names != {expected_name}:
            raise SystemExit(
                f"gold-name mismatch: expected {expected_name}, observed {gold_names}"
            )
        if len(gold_hashes) != 1 or None in gold_hashes:
            raise SystemExit(f"missing or mixed gold hash: {gold_hashes}")
    elif gold_names != {None} or gold_hashes != {None}:
        raise SystemExit(
            f"no-gold panel unexpectedly recorded a gold file: {gold_names} {gold_hashes}"
        )

    for row in rows:
        if row.get("status") == "ok" and row.get("verdict") != "noparse":
            digest = row.get("signature_sha256")
            if not isinstance(digest, str) or len(digest) != 64:
                raise SystemExit(
                    f"successful {row['arm']} row lacks a canonical signature hash"
                )


if __name__ == "__main__":
    main()
