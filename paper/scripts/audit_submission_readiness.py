#!/usr/bin/env python3
"""Report fail-closed SWJ submission readiness without hiding pending gates."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def exists(relative: str) -> bool:
    return (ROOT / relative).is_file()


def nonempty(relative: str) -> bool:
    path = ROOT / relative
    return path.is_file() and path.stat().st_size > 0


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generic_pdf_ready() -> bool:
    pdf = ROOT / "main.pdf"
    sources = [ROOT / "main.tex", ROOT / "references.bib", *ROOT.rglob("*.tex")]
    return (pdf.is_file() and pdf.stat().st_size > 0
            and pdf.read_bytes()[:5] == b"%PDF-"
            and pdf.stat().st_mtime_ns >= max(path.stat().st_mtime_ns for path in sources))


def sage_staging_ready() -> bool:
    receipt = ROOT / "generated" / "sage-staging-verification.json"
    if not receipt.is_file():
        return False
    try:
        payload = json.loads(receipt.read_text())
    except (OSError, json.JSONDecodeError):
        return False
    return (payload.get("status") == "pass"
            and payload.get("source_sha256") == sha256(ROOT / "main.tex")
            and payload.get("class_options") == "Afour,sageh,times")


def review_dispositions_ready() -> bool:
    receipt = ROOT / "reviews" / "disposition-verification.json"
    if not receipt.is_file():
        return False
    try:
        payload = json.loads(receipt.read_text())
    except (OSError, json.JSONDecodeError):
        return False
    return (payload.get("status") == "pass"
            and payload.get("current_manuscript_sha256") == sha256(ROOT / "main.tex")
            and payload.get("reviews") == 7
            and payload.get("undisposed_findings") == 0)


def current_obo_ready() -> bool:
    final = ROOT / "benchmark" / "generated" / "current-final"
    receipt = final / "import-verification.json"
    archive_receipt = final / "evidence-archive-verification.json"
    required = (
        final / "current-aggregate.json",
        final / "current-disagreements.tsv",
        final / "current-results.tex",
        final / "result-records.sha256",
        final / "SHA256SUMS",
        receipt,
        archive_receipt,
    )
    if not all(path.is_file() for path in required):
        return False
    try:
        payload = json.loads(receipt.read_text())
        archive_payload = json.loads(archive_receipt.read_text())
    except (OSError, json.JSONDecodeError):
        return False
    aggregate_digest = sha256(final / "current-aggregate.json")
    record_manifest_digest = sha256(final / "result-records.sha256")
    generated_tex = ROOT / "generated" / "current-results.tex"
    return (payload.get("status") == "verified"
            and payload.get("result_records") == 1512
            and payload.get("ontologies") == 189
            and len(payload.get("baselines", [])) == 8
            and payload.get("aggregate_sha256") == aggregate_digest
            and payload.get("result_record_manifest_sha256") == record_manifest_digest
            and generated_tex.is_file()
            and generated_tex.read_text().splitlines()[0]
                == f"% Generated from aggregate SHA-256 {aggregate_digest}"
            and archive_payload.get("status") == "verified"
            and archive_payload.get("result_records") == 1512
            and archive_payload.get("final_aggregate_sha256") == aggregate_digest
            and isinstance(archive_payload.get("archive_sha256"), str)
            and len(archive_payload["archive_sha256"]) == 64)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=ROOT / "generated" / "submission-readiness.json")
    parser.add_argument("--require-ready", action="store_true")
    args = parser.parse_args()

    manuscript = (ROOT / "main.tex").read_text()
    submission = (ROOT / "SUBMISSION.md").read_text()
    cover = (ROOT / "COVER-LETTER.md").read_text()
    claims = (ROOT / "claims-ledger.tsv").read_text()
    reviews = ("structure", "flow", "clarity", "style", "terms",
               "related-work", "citations")
    gates = [
        {
            "id": "paper_pdf",
            "ready": generic_pdf_ready(),
            "evidence": "paper/main.pdf",
            "detail": "Rendered manuscript PDF is nonempty and newer than its TeX inputs",
        },
        {
            "id": "checklist",
            "ready": not re.search(r"^- \[ \]", submission, re.MULTILINE)
                     and "[TO CONFIRM" not in manuscript,
            "evidence": "paper/SUBMISSION.md",
            "detail": "Every human-facing gate is checked and manuscript declarations are confirmed",
        },
        {
            "id": "current_obo_final",
            "ready": current_obo_ready(),
            "evidence": "paper/benchmark/generated/current-final/import-verification.json; "
                        "paper/generated/current-results.tex",
            "detail": "Strict 1,512-record import, evidence archive, and aggregate-bound TeX verify",
        },
        {
            "id": "current_tables_in_manuscript",
            "ready": r"\input{generated/current-results.tex}" in manuscript
                     and "still running at this manuscript cutoff" not in manuscript,
            "evidence": "paper/main.tex",
            "detail": "Final contemporary tables replace provisional running-job prose",
        },
        {
            "id": "laptop_history",
            "ready": exists("evidence/laptop/SHA256SUMS")
                     and "METH-005\t" in claims
                     and "\tverified" in next(
                         (line for line in claims.splitlines() if line.startswith("METH-005\t")), ""),
            "evidence": "paper/evidence/laptop/SHA256SUMS; paper/claims-ledger.tsv:METH-005",
            "detail": "Pre-standalone evidence is imported, hashed, and adjudicated",
        },
        {
            "id": "independent_reviews",
            "ready": all(nonempty(f"reviews/{name}.md") for name in reviews)
                     and nonempty("reviews/dispositions.tsv")
                     and review_dispositions_ready(),
            "evidence": "paper/reviews/*.md; paper/reviews/dispositions.tsv; paper/reviews/disposition-verification.json",
            "detail": "Seven separate reviews and complete, current-hash author dispositions are retained",
        },
        {
            "id": "sage_template",
            "ready": sage_staging_ready(),
            "evidence": "paper/generated/sage-staging-verification.json",
            "detail": "Source-bound Sage two-column staging build passes without layout or reference errors",
        },
        {
            "id": "cover_letter",
            "ready": "[TO COMPLETE" not in cover and "[TO VERIFY" not in cover,
            "evidence": "paper/COVER-LETTER.md",
            "detail": "Cover letter contains no completion or verification markers",
        },
        {
            "id": "immutable_archive",
            "ready": nonempty("archive/DOI.txt") and nonempty("archive/SHA256SUMS")
                     and nonempty("archive/README.md"),
            "evidence": "paper/archive/{DOI.txt,SHA256SUMS,README.md}",
            "detail": "Immutable public archive has DOI, digest manifest, and top-level instructions",
        },
    ]
    ready = all(gate["ready"] for gate in gates)
    payload = {
        "schema": 1,
        "ready": ready,
        "ready_gates": sum(gate["ready"] for gate in gates),
        "total_gates": len(gates),
        "gates": gates,
        "note": "Run `make -C paper checks` separately; this audit measures submission packaging gates.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    for gate in gates:
        print(f"{'READY' if gate['ready'] else 'PENDING'}\t{gate['id']}\t{gate['detail']}")
    print(f"SUBMISSION_READY\t{str(ready).lower()}\t{payload['ready_gates']}/{len(gates)}")
    if args.require_ready and not ready:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
