#!/usr/bin/env python3
"""Stage and hash the redistributable KM paper artifact before DOI deposit."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
TAG = "v1.3.0"
TAG_COMMIT = "f4738bcdd980a1b2fcc840e4b455d37d447510cb"
EVIDENCE_SHA256 = "98e19518ccfd5a9a9b4321901f85a29e5baf16cdf2319514ef871f55656c5494"
GATE_LOGS = (
    "v1.3-f4738bc-elc-cert.log",
    "v1.3-f4738bc-ht-cert.log",
    "v1.3-f4738bc-cb-cert.log",
    "v1.3-f4738bc-routing-cert.log",
)
BUILD_SUFFIXES = {".aux", ".bbl", ".blg", ".log", ".out", ".toc", ".pyc"}


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def copy_paper(source: Path, target: Path) -> None:
    def ignore(directory: str, names: list[str]) -> set[str]:
        base = Path(directory)
        ignored = set()
        for name in names:
            path = base / name
            if name == "__pycache__" or path.suffix in BUILD_SUFFIXES:
                ignored.add(name)
            if base == source / "archive" and name in {"DOI.txt", "SHA256SUMS"}:
                ignored.add(name)
        return ignored

    shutil.copytree(source, target, ignore=ignore)


def stage(output: Path, evidence: Path, evidence_sidecar: Path, sage_pdf: Path,
          gate_logs: Path, laptop_bundle: Path, replace: bool) -> dict[str, object]:
    if output.exists():
        if not replace:
            raise ValueError(f"output exists: {output}")
        shutil.rmtree(output)
    output.mkdir(parents=True)

    peeled = subprocess.check_output(
        ["git", "rev-list", "-n", "1", TAG], cwd=REPO, text=True
    ).strip()
    if peeled != TAG_COMMIT:
        raise ValueError(f"{TAG} resolves to unexpected commit {peeled}")
    if digest(evidence) != EVIDENCE_SHA256:
        raise ValueError("current-OBO evidence archive digest mismatch")
    sidecar = evidence_sidecar.read_text(encoding="utf-8").split()
    if len(sidecar) != 2 or sidecar[0] != EVIDENCE_SHA256 or Path(sidecar[1]).name != evidence.name:
        raise ValueError("current-OBO evidence sidecar mismatch")
    for path in (ROOT / "main.pdf", sage_pdf, *(gate_logs / name for name in GATE_LOGS)):
        if not path.is_file() or path.stat().st_size == 0:
            raise ValueError(f"required artifact missing or empty: {path}")

    copy_paper(ROOT, output / "paper")
    shutil.copy2(sage_pdf, output / "paper" / "main-swj.pdf")
    source_dir = output / "source"
    source_dir.mkdir()
    source_archive = source_dir / "kobayashi-marust-v1.3.0.tar.gz"
    with source_archive.open("wb") as stream:
        subprocess.run(
            ["git", "archive", "--format=tar.gz", "--prefix=kobayashi-marust-v1.3.0/", TAG],
            cwd=REPO, stdout=stream, check=True,
        )
    laptop_report = json.loads(
        (ROOT / "evidence" / "laptop" / "import-report.json").read_text())
    expected_bundle = laptop_report["history_bundle"]
    if (laptop_bundle.name != expected_bundle["filename"]
            or laptop_bundle.stat().st_size != expected_bundle["bytes"]
            or digest(laptop_bundle) != expected_bundle["sha256"]):
        raise ValueError("laptop prehistory bundle does not match import receipt")
    shutil.copy2(laptop_bundle, source_dir / laptop_bundle.name)

    benchmark_dir = output / "benchmarks" / "current-obo"
    benchmark_dir.mkdir(parents=True)
    shutil.copy2(evidence, benchmark_dir / evidence.name)
    shutil.copy2(evidence_sidecar, benchmark_dir / evidence_sidecar.name)
    certification = output / "certification"
    certification.mkdir()
    for name in GATE_LOGS:
        shutil.copy2(gate_logs / name, certification / name)

    shutil.copy2(ROOT / "archive" / "README.md", output / "README.md")
    receipt = {
        "schema": 1,
        "status": "staged",
        "doi": None,
        "source_tag": TAG,
        "source_commit": TAG_COMMIT,
        "source_archive_sha256": digest(source_archive),
        "generic_pdf_sha256": digest(output / "paper" / "main.pdf"),
        "sage_pdf_sha256": digest(output / "paper" / "main-swj.pdf"),
        "current_obo_evidence_sha256": EVIDENCE_SHA256,
        "laptop_evidence_present": (output / "paper" / "evidence" / "laptop" / "SHA256SUMS").is_file(),
        "independent_reviews_present": (output / "paper" / "reviews" / "disposition-verification.json").is_file(),
    }
    payload_files = sorted(path for path in output.rglob("*") if path.is_file()
                           and path.name not in {"ARTIFACT-RECEIPT.json", "SHA256SUMS"})
    receipt["payload_files"] = len(payload_files)
    receipt["payload_bytes"] = sum(path.stat().st_size for path in payload_files)
    (output / "ARTIFACT-RECEIPT.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    files = sorted(path for path in output.rglob("*") if path.is_file()
                   and path.name != "SHA256SUMS")
    manifest = "".join(f"{digest(path)}  {path.relative_to(output)}\n" for path in files)
    (output / "SHA256SUMS").write_text(manifest, encoding="utf-8")
    subprocess.run(["sha256sum", "-c", "SHA256SUMS"], cwd=output,
                   check=True, stdout=subprocess.DEVNULL)
    receipt["files"] = len(files)
    receipt["bytes_excluding_manifest"] = sum(path.stat().st_size for path in files)
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=REPO / ".work" / "artifacts" / "submission-artifact-staging")
    parser.add_argument("--evidence", type=Path,
                        default=REPO / ".work" / "artifacts" / "current-evidence-v2-from-ibex" /
                        "current-obo-evidence-20260830.tar.gz")
    parser.add_argument("--evidence-sidecar", type=Path,
                        default=REPO / ".work" / "artifacts" / "current-evidence-v2-from-ibex" /
                        "current-obo-evidence-20260830.tar.gz.sha256")
    parser.add_argument("--sage-pdf", type=Path,
                        default=REPO / ".work" / "artifacts" / "paper-sage-staging" /
                        "main-swj.pdf")
    parser.add_argument("--gate-logs", type=Path,
                        default=REPO / ".work" / "worktrees" / "v1.3" / ".work" / "logs")
    parser.add_argument("--laptop-bundle", type=Path,
                        default=Path.home() / "km-paper-laptop-evidence" / "git" /
                        "neuro-symbolic-independence.bundle")
    parser.add_argument("--replace", action="store_true")
    args = parser.parse_args()
    result = stage(args.output, args.evidence, args.evidence_sidecar,
                   args.sage_pdf, args.gate_logs, args.laptop_bundle, args.replace)
    print(f"SUBMISSION_ARTIFACT_STAGED\t{result['files']}\t{result['bytes_excluding_manifest']}")


if __name__ == "__main__":
    main()
