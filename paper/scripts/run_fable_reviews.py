#!/usr/bin/env python3
"""Run the seven independent paper reviews in hash-bound Fable batches."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / "paper"
BRIEF = re.compile(r"^## ([1-7])\. (.+?)\n(.*?)(?=^## [1-7]\. |\Z)", re.MULTILINE | re.DOTALL)
BATCHES = ((1, 2, 3), (4, 5, 6), (7,))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def briefs(path: Path) -> dict[int, tuple[str, str]]:
    parsed = {int(number): (title.strip(), body.strip())
              for number, title, body in BRIEF.findall(path.read_text(encoding="utf-8"))}
    if set(parsed) != set(range(1, 8)):
        raise ValueError(f"expected seven review briefs, found {sorted(parsed)}")
    return parsed


def auth_ready() -> None:
    completed = subprocess.run(["claude", "auth", "status"], cwd=ROOT,
                               capture_output=True, text=True)
    try:
        status = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"cannot parse Claude authentication status: {error}") from error
    if completed.returncode or not status.get("loggedIn"):
        raise RuntimeError("Claude Code is not authenticated; no review was launched")


def prompt(number: int, title: str, body: str, manuscript_sha256: str) -> str:
    return f"""You are independent reviewer {number} of 7 for a research manuscript.
Manuscript SHA-256: {manuscript_sha256}
Assigned aspect: {title}

{body}

Repository root: {ROOT}
Follow the brief's file boundary exactly. Work read-only. Do not edit, create,
delete, commit, or format repository files. Return a self-contained Markdown
report beginning with `# Review {number}: {title}`. Include the manuscript hash,
then `## Major findings`, `## Minor findings`, and `## Verdict`. Number every
finding and cite a section, paragraph opening, citation key, or line number.
Say `None` under a findings heading when no issue exists. Do not discuss any
aspect assigned to another reviewer.
"""


def extract_report(raw: Path, report: Path, number: int, title: str,
                   manuscript_sha256: str) -> dict[str, int]:
    payload = json.loads(raw.read_text(encoding="utf-8"))
    result = payload.get("result")
    if not isinstance(result, str) or not result.strip():
        raise ValueError(f"review {number} has no textual result")
    required = (f"# Review {number}: {title}", manuscript_sha256,
                "## Major findings", "## Minor findings", "## Verdict")
    missing = [value for value in required if value not in result]
    if missing:
        raise ValueError(f"review {number} omits required report fields: {missing}")
    usage = payload.get("usage")
    if not isinstance(usage, dict):
        raise ValueError(f"review {number} omits native usage counters")
    counters = {
        "input_tokens": usage.get("input_tokens", 0),
        "output_tokens": usage.get("output_tokens", 0),
        "cache_creation_tokens": usage.get("cache_creation_input_tokens", 0),
        "cache_read_tokens": usage.get("cache_read_input_tokens", 0),
    }
    if any(not isinstance(value, int) or value < 0 for value in counters.values()):
        raise ValueError(f"review {number} has malformed native usage counters")
    if counters["output_tokens"] <= 0:
        raise ValueError(f"review {number} records no native output tokens")
    report.write_text(result.rstrip() + "\n", encoding="utf-8")
    return counters


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", default="fable")
    parser.add_argument("--output-root", type=Path,
                        default=ROOT / ".work" / "artifacts" / "paper-reviews")
    parser.add_argument("--timeout-seconds", type=int, default=3600)
    args = parser.parse_args()
    subprocess.run([str(ROOT / "tools" / "workspace-preflight.sh")], cwd=ROOT, check=True)
    auth_ready()
    manuscript_sha256 = digest(PAPER / "main.tex")
    source_briefs = briefs(PAPER / "review-prompts.md")
    output = args.output_root / manuscript_sha256
    if output.exists():
        raise ValueError(f"refusing to overwrite review directory: {output}")
    output.mkdir(parents=True)
    manifest = []

    for batch in BATCHES:
        running = []
        for number in batch:
            title, body = source_briefs[number]
            raw = output / f"{number:02d}-{title.lower().replace(' ', '-')}.json"
            error = output / f"{number:02d}-{title.lower().replace(' ', '-')}.stderr"
            report = output / f"{number:02d}-{title.lower().replace(' ', '-')}.md"
            raw_stream = raw.open("w", encoding="utf-8")
            error_stream = error.open("w", encoding="utf-8")
            command = [
                "claude", "--print", "--model", args.model,
                "--dangerously-skip-permissions", "--output-format", "json",
                "--allowed-tools", "Read,Grep,Glob",
                "--disallowed-tools", "Edit,Write,Bash,NotebookEdit,WebFetch,WebSearch",
                "--name", f"km-paper-review-{number}",
                prompt(number, title, body, manuscript_sha256),
            ]
            process = subprocess.Popen(command, cwd=ROOT, stdout=raw_stream,
                                       stderr=error_stream, text=True)
            running.append({"number": number, "title": title, "process": process,
                            "raw": raw, "error": error, "report": report,
                            "stdout": raw_stream, "stderr": error_stream,
                            "started": time.monotonic()})
            print(f"FABLE_REVIEW_STARTED\t{number}\t{process.pid}", flush=True)

        failed = []
        while running:
            time.sleep(5)
            for item in list(running):
                process = item["process"]
                elapsed = time.monotonic() - item["started"]
                if process.poll() is None and elapsed > args.timeout_seconds:
                    process.terminate()
                    try:
                        process.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait()
                if process.poll() is None:
                    continue
                item["stdout"].close(); item["stderr"].close()
                running.remove(item)
                try:
                    if process.returncode:
                        raise RuntimeError(f"Claude exited {process.returncode}")
                    usage = extract_report(item["raw"], item["report"], item["number"],
                                           item["title"], manuscript_sha256)
                    manifest.append({
                        "review": item["number"], "aspect": item["title"],
                        "model": args.model, "manuscript_sha256": manuscript_sha256,
                        "seconds": f"{elapsed:.1f}", "raw_sha256": digest(item["raw"]),
                        "report_sha256": digest(item["report"]), "status": "complete",
                        **usage,
                    })
                    print(f"FABLE_REVIEW_COMPLETE\t{item['number']}\t{elapsed:.1f}", flush=True)
                except Exception as error:
                    failed.append((item["number"], str(error)))
                    print(f"FABLE_REVIEW_FAILED\t{item['number']}\t{error}", flush=True)
            if running:
                active = ",".join(str(item["number"]) for item in running)
                print(f"FABLE_REVIEW_MONITOR\t{active}", flush=True)
        if failed:
            raise RuntimeError(f"review batch failed; later batches not launched: {failed}")

    manifest.sort(key=lambda row: row["review"])
    fields = ("review", "aspect", "model", "manuscript_sha256", "seconds",
              "input_tokens", "output_tokens", "cache_creation_tokens",
              "cache_read_tokens", "raw_sha256", "report_sha256", "status")
    lines = ["\t".join(fields)]
    lines.extend("\t".join(str(row[field]) for field in fields) for row in manifest)
    (output / "manifest.tsv").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"FABLE_REVIEWS_OK\t7\t{manuscript_sha256}")


if __name__ == "__main__":
    main()
