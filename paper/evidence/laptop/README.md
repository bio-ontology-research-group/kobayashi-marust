# Laptop AgentsView aggregate evidence

Collected 2026-08-31 on the original laptop from the existing frozen
AgentsView database (`~/.agentsview/sessions.db`). `agentsview sync` was
never invoked. AgentsView version: v0.33.1 (see `version.txt`).

UTC half-open reporting window: `2026-02-01` through `2026-07-11`.
The workstation evidence begins on 2026-07-11, so this window ends at that
boundary and does not overlap the pinned workstation reports.

## Observed activity boundaries (report requested in evidence-needed.md)

- Project `kobayashi_marust` (the standalone KM repository): first observed
  session 2026-06-10T05:42:36Z, i.e. after the first standalone commit of
  2026-06-02. 681 sessions (subagent children included) inside the window.
- Project `neuro_symbolic_independence` (the original paper repository in
  which KM was conceived): first observed session 2026-05-15T04:13:41Z.
  This is the earliest KM-relevant activity retained on the laptop and it
  predates the 2026-06-02 standalone cutoff; the window was therefore opened
  early (2026-02-01) as instructed. 126 sessions inside the window.
- Project `neuro_symbolic`: a single opencode session on 2026-02-02
  ("AGENTS.md setup with guidelines", repository housekeeping). Included for
  completeness; it does not appear to be the KM conception conversation.

## Deviations from paper/scripts/collect_laptop_agentsview.sh

The laptop runs agentsview v0.33.1, older than the version the collection
script was written against. Checked on the laptop before querying, as the
evidence request requires:

1. `agentsview activity report` does not exist in v0.33.1. In its place,
   `sessions-<project>.json` provides the full per-session metadata from
   `agentsview session list --include-one-shot --include-automated
   --include-children` (paginated to completion): session and subagent
   identifiers, agent and model attribution, start/end timestamps, message
   and tool-failure counters, peak context and output token counters,
   outcomes, and health signals.
2. `agentsview stats` in v0.33.1 has no `--no-sync`, `--include-one-shot`,
   or `--include-automated` flags. `stats-<project>.json` was produced
   without them. The v0.33.1 `stats` command reads the existing database and
   offers no sync switch; the database was not modified by this collection.
3. `agentsview usage daily` in v0.33.1 has no project filter, so
   `usage-daily-machine-wide.json` is the native machine-wide daily
   aggregate over the window (all laptop projects, per-model breakdown).
   Treat it as an upper bound when reconciling with the project-filtered
   session and stats reports; per-project token/cost attribution comes from
   `sessions-*.json` and `stats-*.json`.

## Privacy handling

- No prompts, responses, commands, or tool results are included. The
  `first_message` field returned by `session list` was removed from every
  record; the `machine` field was replaced by the fixed token `laptop`.
- `config-effective.txt` documents the effective configuration; the only
  key in `~/.agentsview/config.toml` was a credential (`cursor_secret`) and
  was removed. No AgentsView path or project restrictions exist on the
  laptop, so the database covers all default agent session roots.
- The SQLite archive itself is not included (marked optional in the
  request).

Verify with `sha256sum -c SHA256SUMS` from this directory.
