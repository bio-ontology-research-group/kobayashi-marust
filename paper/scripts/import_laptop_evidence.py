#!/usr/bin/env python3
"""Import the privacy-preserving laptop evidence and render paper counters."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil


ROOT = Path(__file__).resolve().parents[1]


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def verify_manifest(root: Path) -> None:
    for line in (root / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        expected, name = line.split(None, 1)
        path = root / name.strip()
        if not path.is_file() or digest(path) != expected:
            raise ValueError(f"digest mismatch: {path}")


def session_summary(path: Path, stats_path: Path) -> dict[str, object]:
    data = json.loads(path.read_text(encoding="utf-8"))
    rows = data["sessions"]
    if len(rows) != data["session_count"]:
        raise ValueError(f"session count mismatch: {path}")
    stats = json.loads(stats_path.read_text(encoding="utf-8"))
    top_level = stats["totals"]["sessions_all"]
    return {
        "project": data["project"],
        "sessions": len(rows),
        "top_level": top_level,
        "children": len(rows) - top_level,
        "first_started_at": data["first_started_at"],
        "last_started_at": data["last_started_at"],
        "output_tokens": sum(row.get("total_output_tokens", 0) for row in rows
                             if row.get("has_total_output_tokens")),
        "messages": sum(row.get("message_count", 0) for row in rows),
        "tool_failure_signals": sum(row.get("tool_failure_signal_count", 0) for row in rows),
        "tool_retries": sum(row.get("tool_retry_count", 0) for row in rows),
        "edit_churn": sum(row.get("edit_churn_count", 0) for row in rows),
        "agents": dict(sorted({agent: sum(r["agent"] == agent for r in rows)
                               for agent in {r["agent"] for r in rows}}.items())),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--history", type=Path, default=Path.home() / "km-paper-laptop-evidence")
    parser.add_argument("--agentsview", type=Path, default=Path.home() / "km-paper-laptop-agentsview")
    parser.add_argument("--output", type=Path, default=ROOT / "evidence" / "laptop")
    args = parser.parse_args()
    verify_manifest(args.history)
    verify_manifest(args.agentsview)

    if args.output.exists():
        shutil.rmtree(args.output)
    args.output.mkdir(parents=True)
    for name in ("README.md", "version.txt", "config-effective.txt",
                 "sessions-kobayashi_marust.json",
                 "sessions-neuro_symbolic_independence.json",
                 "sessions-neuro_symbolic.json", "stats-kobayashi_marust.json",
                 "stats-neuro_symbolic_independence.json", "stats-neuro_symbolic.json",
                 "usage-daily-machine-wide.json"):
        shutil.copy2(args.agentsview / name, args.output / name)
    shutil.copy2(args.history / "README.txt", args.output / "history-README.txt")
    for name in ("pre-cutoff-commits.tsv", "show-ref.txt", "working-tree-status.txt"):
        shutil.copy2(args.history / "git" / name, args.output / name)
    shutil.copytree(args.history / "memory", args.output / "memory")

    summaries = {
        name: session_summary(args.agentsview / f"sessions-{name}.json",
                              args.agentsview / f"stats-{name}.json")
        for name in ("kobayashi_marust", "neuro_symbolic_independence", "neuro_symbolic")
    }
    report = {
        "schema": 1,
        "agentsview_version": (args.agentsview / "version.txt").read_text().strip(),
        "source_manifests_verified": True,
        "history_bundle": {
            "filename": "neuro-symbolic-independence.bundle",
            "sha256": digest(args.history / "git" / "neuro-symbolic-independence.bundle"),
            "bytes": (args.history / "git" / "neuro-symbolic-independence.bundle").stat().st_size,
            "archived_separately": True,
        },
        "projects": summaries,
        "attribution_policy": {
            "kobayashi_marust": "KM-specific retained project telemetry",
            "neuro_symbolic_independence": "containing-project upper bound; not additive as KM usage",
            "neuro_symbolic": "excluded housekeeping session",
            "machine_wide_daily": "upper bound only; v0.33.1 lacked project filtering",
        },
    }
    (args.output / "import-report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    files = sorted(path for path in args.output.rglob("*")
                   if path.is_file() and path.name != "SHA256SUMS")
    (args.output / "SHA256SUMS").write_text(
        "".join(f"{digest(path)}  {path.relative_to(args.output)}\n" for path in files),
        encoding="utf-8")

    km = summaries["kobayashi_marust"]
    parent = summaries["neuro_symbolic_independence"]
    integer = lambda value: f"{value:,}"
    tex = [
        "% Generated by scripts/import_laptop_evidence.py; do not edit.",
        rf"\newcommand{{\KMLaptopAVVersion}}{{0.33.1}}",
        rf"\newcommand{{\KMLaptopSessions}}{{{integer(km['sessions'])}}}",
        rf"\newcommand{{\KMLaptopTopSessions}}{{{integer(km['top_level'])}}}",
        rf"\newcommand{{\KMLaptopSubagents}}{{{integer(km['children'])}}}",
        rf"\newcommand{{\KMLaptopOutputTokens}}{{{integer(km['output_tokens'])}}}",
        rf"\newcommand{{\KMLaptopMessages}}{{{integer(km['messages'])}}}",
        rf"\newcommand{{\KMLaptopFirstDate}}{{{str(km['first_started_at'])[:10]}}}",
        rf"\newcommand{{\KMLaptopLastDate}}{{{str(km['last_started_at'])[:10]}}}",
        rf"\newcommand{{\KMParentProjectSessions}}{{{integer(parent['sessions'])}}}",
        rf"\newcommand{{\KMParentProjectOutputTokens}}{{{integer(parent['output_tokens'])}}}",
        rf"\newcommand{{\KMParentProjectFirstDate}}{{{str(parent['first_started_at'])[:10]}}}",
    ]
    (ROOT / "generated" / "laptop-evidence-summary.tex").write_text(
        "\n".join(tex) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
