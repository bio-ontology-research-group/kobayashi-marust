# AgentsView process-usage evidence

These reports were generated with AgentsView v0.41.1 (commit `a902515a`) from
the retained local Claude Code and Codex session archives.  Sync was restricted
to sessions whose working directory began with
`/home/leechuck/Public/software/kobayashi-marust`.  AgentsView resolved the
project to the Git remote
`github.com/bio-ontology-research-group/kobayashi-marust`.

The fixed reporting window was 2026-06-02 00:00:00 UTC through 2026-08-31
00:00:00 UTC.  The first observed usage was 2026-07-11 and the final report was
generated during 2026-08-30, so the activity report marks the final bucket as
partial.  The commands were equivalent to:

```text
agentsview usage daily --all --since 2026-06-02 --until 2026-08-31 --timezone UTC --breakdown --no-sync --json
agentsview stats --include-project kobayashi_marust --since 2026-06-02 --until 2026-08-31 --timezone UTC --include-one-shot --include-automated --format json
agentsview activity report --project kobayashi_marust --preset custom --from 2026-06-02T00:00:00Z --to 2026-08-31T00:00:00Z --timezone UTC --bucket 1d --no-sync --json
```

The v1.3.0 release commit is timestamped 2026-08-30 06:07:24 UTC.  Because the
native usage export is daily, its final bucket cannot separate pre-tag release
work from post-tag evidence reconstruction and manuscript preparation.  The
paper therefore describes these totals as retained KM project activity rather
than implementation-only effort.

The local AgentsView configuration also contained authentication material, so
it is deliberately excluded.  Its non-secret acquisition settings were:

```toml
claude_project_dirs = ["/home/leechuck/.claude/projects"]
codex_sessions_dirs = ["/home/leechuck/.codex/sessions"]
sync_include_cwd_prefixes = ["/home/leechuck/Public/software/kobayashi-marust"]
```

The AgentsView daemon was stopped before these final reports were generated,
so all three query the same frozen SQLite snapshot.  `usage-daily-all.json`
and `activity-km-20260602-20260831.json` agree on 28,910,472 native output
tokens.  The `model_mix.by_tokens` field in the stats
report instead measures tokenized message content and differs for Claude; the
paper does not combine it with API usage counters.  Cost fields are retained
for schema fidelity but are not reported as expenditure because AgentsView
used fallback prices for all four observed model names.

The reports contain aggregate telemetry and opaque project identifiers.  They
contain no prompt text, response text, commands, or tool results.  SHA-256
digests are listed in `SHA256SUMS` and verified by the paper renderer.
