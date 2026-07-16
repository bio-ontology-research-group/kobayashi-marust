#!/usr/bin/env python3
"""Sanity-check an active route-proof result tree and fail on systemic errors."""

import argparse
import glob
import json
import os
from collections import Counter, defaultdict


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("result_root")
    parser.add_argument("--minimum-rows", type=int, default=1)
    parser.add_argument("--expected-routes", type=int, default=34)
    args = parser.parse_args()

    files = glob.glob(os.path.join(args.result_root, "*", "*.jsonl"))
    if len(files) < args.minimum_rows:
        raise SystemExit(
            f"WAIT rows={len(files)} minimum={args.minimum_rows}"
        )

    statuses = Counter()
    verdicts = Counter()
    hashes = Counter()
    panels = defaultdict(set)
    malformed = []
    for path in files:
        try:
            with open(path, encoding="utf-8") as handle:
                lines = [line for line in handle if line.strip()]
            if len(lines) != 1:
                raise ValueError(f"{len(lines)} non-empty lines")
            row = json.loads(lines[0])
            for field in ("ont", "arm", "status", "verdict", "binary_sha256"):
                if not row.get(field):
                    raise ValueError(f"missing {field}")
            if row["status"] == "ok" and not row.get("signature_sha256"):
                raise ValueError("ok row lacks signature")
        except Exception as exc:
            malformed.append((path, str(exc)))
            continue
        statuses[row["status"]] += 1
        verdicts[row["verdict"]] += 1
        hashes[row["binary_sha256"]] += 1
        panels[row["ont"]].add(row["arm"])

    if malformed:
        raise SystemExit(f"FAIL malformed={malformed[:5]}")
    if len(hashes) != 1:
        raise SystemExit(f"FAIL binary_hashes={dict(hashes)}")
    if statuses["error"]:
        raise SystemExit(f"FAIL execution_errors={statuses['error']}")
    complete = sum(len(routes) == args.expected_routes for routes in panels.values())
    print(
        f"OK rows={len(files)} ontologies={len(panels)} complete={complete} "
        f"status={dict(statuses)} verdict={dict(verdicts)} "
        f"binary={next(iter(hashes))}"
    )


if __name__ == "__main__":
    main()
