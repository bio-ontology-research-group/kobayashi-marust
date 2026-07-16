#!/usr/bin/env python3
"""Print the Slurm array indices whose 34-route panels need to be resumed."""

import argparse
import json
import os


ROUTES = (
    "auto default default8 default1 "
    "production_all production_all8 production_all1 "
    "cb_plain16 cb_plain8 cb_plain1 cb_absorb16 cb_absorb8 cb_absorb1 "
    "cb_trigger16 cb_trigger8 cb_trigger1 cb_absorb_portfolio16 "
    "elc elc_cert lean ht_general ht_qo ht_shoq ht_card ht_bridge "
    "ht_features ht_full ht_rules tableau tab_race card_fn nominals seq_on seq_off"
).split()


def valid(path, ontology, route, binary_sha):
    try:
        with open(path, encoding="utf-8") as handle:
            lines = [line for line in handle if line.strip()]
        if len(lines) != 1:
            return False
        row = json.loads(lines[0])
    except (OSError, ValueError):
        return False
    if (
        row.get("ont") != ontology
        or row.get("arm") != route
        or row.get("requested_route") != route
        or row.get("binary_sha256") != binary_sha
        or row.get("status") == "error"
    ):
        return False
    return row.get("status") != "ok" or bool(row.get("signature_sha256"))


def compress(indices):
    if not indices:
        return ""
    ranges = []
    start = previous = indices[0]
    for index in indices[1:]:
        if index == previous + 1:
            previous = index
            continue
        ranges.append(str(start) if start == previous else f"{start}-{previous}")
        start = previous = index
    ranges.append(str(start) if start == previous else f"{start}-{previous}")
    return ",".join(ranges)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("proof_root")
    parser.add_argument("ontology_list")
    args = parser.parse_args()

    with open(os.path.join(args.proof_root, "km.sha256"), encoding="utf-8") as handle:
        binary_sha = handle.read().split()[0]
    with open(args.ontology_list, encoding="utf-8") as handle:
        ontologies = [line.strip() for line in handle if line.strip()]

    resume = []
    valid_rows = 0
    for index, ontology in enumerate(ontologies):
        complete = True
        for route in ROUTES:
            path = os.path.join(
                args.proof_root, "results", route, ontology + ".jsonl"
            )
            if valid(path, ontology, route, binary_sha):
                valid_rows += 1
            else:
                complete = False
        if not complete:
            resume.append(index)

    print(
        json.dumps(
            {
                "binary_sha256": binary_sha,
                "valid_rows": valid_rows,
                "expected_rows": len(ontologies) * len(ROUTES),
                "complete_panels": len(ontologies) - len(resume),
                "resume_panels": len(resume),
                "array_spec": compress(resume),
                "indices": resume,
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
