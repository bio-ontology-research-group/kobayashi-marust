#!/usr/bin/env python3
"""Verify that every imported review finding has an explicit author disposition."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / "paper"
REPORTS = {
    1: "structure.md", 2: "flow.md", 3: "clarity.md", 4: "style.md",
    5: "terms.md", 6: "related-work.md", 7: "citations.md",
}
FINDING = re.compile(r"^(?:#{3,4}\s*)?(\d+)[.)]\s+\S")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def section(text: str, heading: str, next_heading: str) -> str:
    start = text.find(heading)
    if start < 0:
        raise ValueError(f"review omits heading: {heading}")
    start += len(heading)
    end = text.find(next_heading, start)
    if end < 0:
        raise ValueError(f"review omits heading after {heading}: {next_heading}")
    return text[start:end]


def report_findings(path: Path, review: int) -> set[tuple[int, str, int]]:
    text = path.read_text(encoding="utf-8")
    answer = set()
    for severity, first, following in (
            ("major", "## Major findings", "## Minor findings"),
            ("minor", "## Minor findings", "## Verdict")):
        body = section(text, first, following)
        numbers = [int(match.group(1)) for line in body.splitlines()
                   if (match := FINDING.match(line.strip()))]
        if len(numbers) != len(set(numbers)):
            raise ValueError(f"duplicate {severity} finding number in review {review}")
        if numbers and sorted(numbers) != list(range(1, len(numbers) + 1)):
            raise ValueError(f"non-consecutive {severity} findings in review {review}")
        if not numbers and not re.search(r"\bNone\b", body, re.IGNORECASE):
            raise ValueError(f"review {review} has neither numbered nor explicit empty {severity} findings")
        answer.update((review, severity, number) for number in numbers)
    return answer


def verify(reviews: Path, manuscript: Path, dispositions: Path) -> dict:
    usage_path = reviews / "review-usage.tsv"
    with usage_path.open(encoding="utf-8", newline="") as stream:
        usage = list(csv.DictReader(stream, delimiter="\t"))
    if len(usage) != 7:
        raise ValueError("review usage manifest does not contain seven reviews")
    by_number = {int(row["review"]): row for row in usage}
    if set(by_number) != set(REPORTS):
        raise ValueError("review usage index set differs")
    reviewed_hashes = {row["manuscript_sha256"] for row in usage}
    if len(reviewed_hashes) != 1:
        raise ValueError("reviews target different manuscript hashes")
    findings = set()
    report_hashes = {}
    for number, name in REPORTS.items():
        path = reviews / name
        actual = digest(path)
        if actual != by_number[number]["report_sha256"]:
            raise ValueError(f"imported report digest mismatch: {number}")
        report_hashes[str(number)] = actual
        findings.update(report_findings(path, number))

    with dispositions.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    required = {"review", "severity", "finding", "disposition", "rationale",
                "manuscript_action"}
    if rows and set(rows[0]) != required:
        raise ValueError("unexpected disposition schema")
    if not rows:
        with dispositions.open(encoding="utf-8", newline="") as stream:
            reader = csv.DictReader(stream, delimiter="\t")
            if set(reader.fieldnames or ()) != required:
                raise ValueError("unexpected disposition schema")
    disposed = set()
    for row in rows:
        try:
            key = (int(row["review"]), row["severity"], int(row["finding"]))
        except ValueError as error:
            raise ValueError("non-numeric disposition index") from error
        if key in disposed:
            raise ValueError(f"duplicate disposition: {key}")
        if key not in findings:
            raise ValueError(f"disposition refers to an unknown finding: {key}")
        if row["disposition"] not in {"accepted", "rejected", "deferred"}:
            raise ValueError(f"unknown disposition decision: {row['disposition']}")
        if len(row["rationale"].strip()) < 10 or not row["manuscript_action"].strip():
            raise ValueError(f"disposition lacks rationale or manuscript action: {key}")
        disposed.add(key)
    missing = sorted(findings - disposed)
    if missing:
        raise ValueError(f"undisposed review findings: {missing}")
    current_hash = digest(manuscript)
    return {
        "schema": 1,
        "status": "pass",
        "reviews": 7,
        "reviewed_manuscript_sha256": next(iter(reviewed_hashes)),
        "current_manuscript_sha256": current_hash,
        "report_sha256": report_hashes,
        "findings": len(findings),
        "undisposed_findings": 0,
        "disposition_counts": {
            decision: sum(row["disposition"] == decision for row in rows)
            for decision in ("accepted", "rejected", "deferred")
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reviews", type=Path, default=PAPER / "reviews")
    parser.add_argument("--manuscript", type=Path, default=PAPER / "main.tex")
    parser.add_argument("--dispositions", type=Path,
                        default=PAPER / "reviews" / "dispositions.tsv")
    parser.add_argument("--output", type=Path,
                        default=PAPER / "reviews" / "disposition-verification.json")
    args = parser.parse_args()
    report = verify(args.reviews, args.manuscript, args.dispositions)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(f"REVIEW_DISPOSITIONS_OK\t{report['findings']}\t0")


if __name__ == "__main__":
    main()
