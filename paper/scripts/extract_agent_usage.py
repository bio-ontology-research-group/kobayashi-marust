#!/usr/bin/env python3
"""Extract AgentView-style usage statistics from retained KM agent logs.

The extractor publishes aggregate telemetry and hash-bound per-session rows,
never prompt, response, command, or tool-result text.  Claude API messages are
deduplicated by message id because one response can occupy several JSONL
events.  Codex token events are deduplicated globally by timestamp and
cumulative counter because forked rollout files retain shared history.
"""

from __future__ import annotations

import collections
import csv
import datetime as dt
import hashlib
import json
import pathlib
import subprocess


ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / "paper" / "generated"
CLAUDE_ROOT = pathlib.Path(
    "/home/leechuck/.claude/projects/"
    "-home-leechuck-Public-software-kobayashi-marust"
)
CODEX_ROOT = pathlib.Path("/home/leechuck/.codex/sessions")
REPO = "/home/leechuck/Public/software/kobayashi-marust"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def timestamp(value: str) -> dt.datetime | None:
    try:
        return dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    except (TypeError, ValueError):
        return None


def rg_json(pattern: str, paths: list[pathlib.Path]) -> list[dict]:
    if not paths:
        return []
    process = subprocess.run(
        ["rg", "--no-filename", pattern, *map(str, paths)],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if process.returncode not in (0, 1):
        raise RuntimeError(process.stderr.decode(errors="replace"))
    rows = []
    for line in process.stdout.splitlines():
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError:
            continue
    return rows


def claude_usage() -> tuple[dict, list[dict]]:
    calls: dict[str, dict] = {}
    tools: set[str] = set()
    sessions: dict[str, dict] = {}
    failures = 0
    for path in sorted(CLAUDE_ROOT.glob("*.jsonl")):
        raw = path.read_bytes()
        session_id = path.stem
        record = {
            "platform": "Claude Code", "session_id": session_id,
            "source_sha256": sha(raw), "first_timestamp_utc": "",
            "last_timestamp_utc": "", "model_calls": 0, "tool_calls": 0,
            "input_tokens": 0, "cached_input_tokens": 0,
            "cache_creation_input_tokens": 0, "output_tokens": 0,
            "reasoning_output_tokens": "not_recorded", "failed_calls": 0,
        }
        seen_tools: set[str] = set()
        times: list[dt.datetime] = []
        for line in raw.splitlines():
            try:
                event = json.loads(line)
            except (UnicodeDecodeError, json.JSONDecodeError):
                continue
            parsed_time = timestamp(event.get("timestamp", ""))
            if parsed_time:
                times.append(parsed_time)
            if event.get("isApiErrorMessage"):
                record["failed_calls"] += 1
                failures += 1
            if event.get("type") != "assistant":
                continue
            message = event.get("message") or {}
            model = message.get("model")
            message_id = message.get("id")
            usage = message.get("usage") or {}
            if message_id and model and model != "<synthetic>" and message_id not in calls:
                calls[message_id] = {
                    "session": session_id, "model": model,
                    "input_tokens": int(usage.get("input_tokens", 0)),
                    "cached_input_tokens": int(usage.get("cache_read_input_tokens", 0)),
                    "cache_creation_input_tokens": int(usage.get("cache_creation_input_tokens", 0)),
                    "output_tokens": int(usage.get("output_tokens", 0)),
                }
            for item in message.get("content") or []:
                if isinstance(item, dict) and item.get("type") == "tool_use" and item.get("id"):
                    seen_tools.add(str(item["id"])); tools.add(str(item["id"]))
        own_calls = [value for value in calls.values() if value["session"] == session_id]
        record["model_calls"] = len(own_calls)
        record["tool_calls"] = len(seen_tools)
        for key in ("input_tokens", "cached_input_tokens", "cache_creation_input_tokens", "output_tokens"):
            record[key] = sum(value[key] for value in own_calls)
        if times:
            record["first_timestamp_utc"] = min(times).isoformat()
            record["last_timestamp_utc"] = max(times).isoformat()
        sessions[session_id] = record
    models = collections.Counter(call["model"] for call in calls.values())
    summary = {
        "platform": "Claude Code", "sessions": len(sessions),
        "sessions_with_model_calls": sum(row["model_calls"] > 0 for row in sessions.values()),
        "model_calls": len(calls), "tool_calls": len(tools), "failed_calls": failures,
        "models": dict(sorted(models.items())),
    }
    for key in ("input_tokens", "cached_input_tokens", "cache_creation_input_tokens", "output_tokens"):
        summary[key] = sum(call[key] for call in calls.values())
    summary["reasoning_output_tokens"] = "not_recorded"
    return summary, list(sessions.values())


def codex_paths() -> list[pathlib.Path]:
    process = subprocess.run(
        ["rg", "-l", "-F", REPO, str(CODEX_ROOT), "-g", "*.jsonl"],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if process.returncode not in (0, 1):
        raise RuntimeError(process.stderr.decode(errors="replace"))
    return [pathlib.Path(line.decode()) for line in process.stdout.splitlines()]


def codex_usage() -> tuple[dict, list[dict]]:
    paths = codex_paths()
    token_events = rg_json(r'"type":"token_count"', paths)
    context_events = rg_json(r'"type":"turn_context"', paths)
    models = collections.Counter()
    for event in context_events:
        model = (event.get("payload") or {}).get("model")
        turn = (event.get("payload") or {}).get("turn_id")
        if model and turn:
            models[(str(turn), str(model))] += 1
    unique_models = collections.Counter()
    for (_turn, model) in models:
        unique_models[model] += 1

    # Codex rollout forks retain and sometimes re-emit ancestral token and tool
    # events.  The schema does not carry a billing-event identifier that lets
    # us prove a disjoint partition.  Session identities are recoverable from
    # each file's first session_meta event; aggregate calls/tokens/tools are not.
    metas: dict[str, dict] = {}
    for path in paths:
        events = rg_json(r'"type":"session_meta"', [path])
        if not events:
            continue
        payload = events[0].get("payload") or {}
        ident = str(payload.get("id") or path.stem)
        if payload.get("cwd") == REPO:
            metas[ident] = payload
    times = [timestamp(event.get("timestamp", "")) for event in token_events]
    times = [value for value in times if value]
    summary = {
        "platform": "Codex", "sessions": len(metas),
        "sessions_with_model_calls": "not_derivable_from_forked_rollouts",
        "model_calls": "not_identifiable_from_forked_rollouts",
        "tool_calls": "not_identifiable_from_forked_rollouts",
        "failed_calls": "not_uniformly_recorded", "models": dict(sorted(unique_models.items())),
        "input_tokens": "not_identifiable_from_forked_rollouts",
        "cached_input_tokens": "not_identifiable_from_forked_rollouts",
        "cache_creation_input_tokens": "not_recorded",
        "output_tokens": "not_identifiable_from_forked_rollouts",
        "reasoning_output_tokens": "not_identifiable_from_forked_rollouts",
        "first_timestamp_utc": min(times).isoformat() if times else "",
        "last_timestamp_utc": max(times).isoformat() if times else "",
        "deduplication": "no aggregate published: retained forks cannot be proved disjoint",
    }
    rows = [{
        "platform": "Codex", "session_id": ident,
        "source_sha256": "not_computed_large_mutable_rollout",
        "first_timestamp_utc": str(payload.get("timestamp", "")),
        "last_timestamp_utc": "reported_in_platform_aggregate",
        "model_calls": "not_identifiable_from_forked_rollouts",
        "tool_calls": "not_identifiable_from_forked_rollouts",
        "input_tokens": "not_identifiable_from_forked_rollouts",
        "cached_input_tokens": "not_identifiable_from_forked_rollouts",
        "cache_creation_input_tokens": "not_recorded",
        "output_tokens": "not_identifiable_from_forked_rollouts",
        "reasoning_output_tokens": "not_identifiable_from_forked_rollouts",
        "failed_calls": "not_uniformly_recorded",
    } for ident, payload in sorted(metas.items())]
    return summary, rows


def fmt(value: object) -> str:
    if isinstance(value, int):
        return f"{value:,}"
    if str(value).startswith("not_"):
        return "--"
    return str(value)


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    claude, claude_rows = claude_usage()
    codex, codex_rows = codex_usage()
    report = {
        "schema": 1,
        "scope": "retained KM-specific local agent logs; incomplete before the recorded windows",
        "privacy": "no prompt, response, command, or tool-result text exported",
        "platforms": [claude, codex],
    }
    report_path = OUT / "agent-usage.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    rows = claude_rows + codex_rows
    with (OUT / "agent-usage-sessions.tsv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, delimiter="\t", lineterminator="\n", fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    tex = f"""% Generated by paper/scripts/extract_agent_usage.py. Do not edit.
\\newcommand{{\\KMClaudeUsageSessions}}{{{fmt(claude['sessions'])}}}
\\newcommand{{\\KMClaudeUsageCalls}}{{{fmt(claude['model_calls'])}}}
\\newcommand{{\\KMClaudeUsageTools}}{{{fmt(claude['tool_calls'])}}}
\\newcommand{{\\KMClaudeInputTokens}}{{{fmt(claude['input_tokens'])}}}
\\newcommand{{\\KMClaudeCacheReadTokens}}{{{fmt(claude['cached_input_tokens'])}}}
\\newcommand{{\\KMClaudeCacheCreateTokens}}{{{fmt(claude['cache_creation_input_tokens'])}}}
\\newcommand{{\\KMClaudeOutputTokens}}{{{fmt(claude['output_tokens'])}}}
\\newcommand{{\\KMCodexUsageSessions}}{{{fmt(codex['sessions'])}}}
\\newcommand{{\\KMCodexUsageCalls}}{{{fmt(codex['model_calls'])}}}
\\newcommand{{\\KMCodexUsageTools}}{{{fmt(codex['tool_calls'])}}}
\\newcommand{{\\KMCodexInputTokens}}{{{fmt(codex['input_tokens'])}}}
\\newcommand{{\\KMCodexCacheReadTokens}}{{{fmt(codex['cached_input_tokens'])}}}
\\newcommand{{\\KMCodexOutputTokens}}{{{fmt(codex['output_tokens'])}}}
\\newcommand{{\\KMCodexReasoningTokens}}{{{fmt(codex['reasoning_output_tokens'])}}}
"""
    (OUT / "agent-usage-summary.tex").write_text(tex, encoding="utf-8")
    print(f"AGENT_USAGE_OK\t{sha(report_path.read_bytes())}")


if __name__ == "__main__":
    main()
