#!/usr/bin/env python3
"""Select the predeclared, outcome-independent BioPortal benchmark panel."""

from __future__ import annotations

import argparse
from collections import defaultdict
import csv
import hashlib
from pathlib import Path


SEED = "km-bioportal-20260830-v1"
SIZE_BINS = (("<1k", 0, 1_000), ("1k--10k", 1_000, 10_000),
             ("10k--100k", 10_000, 100_000), (">=100k", 100_000, None))


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def profile(path: Path) -> tuple[int, dict[str, bool]]:
    logical_axioms = None
    values: dict[str, bool] = {}
    terminal = None
    with path.open(encoding="utf-8") as stream:
        for raw in stream:
            fields = raw.rstrip("\n").split("\t")
            if len(fields) == 3 and fields[:2] == ["M", "logical_axioms"]:
                logical_axioms = int(fields[2])
            elif len(fields) == 4 and fields[0] == "P" and fields[1] in {"OWL2DL", "OWL2EL"}:
                values[fields[1]] = fields[2] == "true"
            elif fields == ["Z", "complete"]:
                terminal = "complete"
    if logical_axioms is None or set(values) != {"OWL2DL", "OWL2EL"} or terminal != "complete":
        raise ValueError(f"incomplete profile {path}")
    return logical_axioms, values


def size_bin(count: int) -> str:
    for label, lower, upper in SIZE_BINS:
        if count >= lower and (upper is None or count < upper):
            return label
    raise AssertionError("unreachable")


def expressivity_bin(values: dict[str, bool]) -> str:
    if values["OWL2EL"]:
        return "OWL 2 EL"
    if values["OWL2DL"]:
        return "OWL 2 DL, non-EL"
    return "outside OWL 2 DL"


def rank(row: dict[str, str]) -> str:
    digest = hashlib.sha256()
    for value in (SEED, row["acronym"], row["submission_id"], row["source_sha256"]):
        encoded = value.encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "big")); digest.update(encoded)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidates", required=True, type=Path)
    parser.add_argument("--profiles", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--quota", type=int, default=10)
    args = parser.parse_args()
    if args.quota <= 0:
        raise ValueError("quota must be positive")

    candidates = read_tsv(args.candidates)
    required = {"acronym", "submission_id", "source_sha256", "eligible", "exclusion_reason"}
    if not candidates or any(not required.issubset(row) for row in candidates):
        raise ValueError("candidate manifest schema mismatch")
    if len({row["acronym"] for row in candidates}) != len(candidates):
        raise ValueError("duplicate BioPortal acronym")

    cells: dict[tuple[str, str], list[dict[str, str]]] = defaultdict(list)
    output_rows = []
    for row in candidates:
        result = dict(row)
        result.update(logical_axioms="", size_bin="", expressivity_bin="", selection_rank="",
                      selected="false", selection_reason=row["exclusion_reason"])
        if row["eligible"] == "true":
            count, values = profile(args.profiles / f"{row['acronym']}.tsv")
            result.update(logical_axioms=str(count), size_bin=size_bin(count),
                          expressivity_bin=expressivity_bin(values), selection_rank=rank(row),
                          selection_reason="cell_quota")
            cells[(result["size_bin"], result["expressivity_bin"])].append(result)
        elif row["eligible"] != "false" or not row["exclusion_reason"]:
            raise ValueError(f"invalid exclusion for {row['acronym']}")
        output_rows.append(result)

    selected = set()
    for members in cells.values():
        for row in sorted(members, key=lambda item: (item["selection_rank"], item["acronym"]))[:args.quota]:
            selected.add(row["acronym"])
    for row in output_rows:
        if row["acronym"] in selected:
            row["selected"] = "true"
            row["selection_reason"] = "selected_by_predeclared_cell_quota"
        elif row["eligible"] == "true":
            row["selection_reason"] = "not_in_lowest_cell_ranks"

    output_rows.sort(key=lambda row: row["acronym"])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(args.output) + ".part")
    with temporary.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=output_rows[0].keys(), delimiter="\t")
        writer.writeheader(); writer.writerows(output_rows)
    temporary.replace(args.output)
    print(f"BIOPORTAL_SAMPLE_OK\t{len(selected)}\t{len(cells)}")


if __name__ == "__main__":
    main()
