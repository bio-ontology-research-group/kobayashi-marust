# Original-laptop evidence: received and adjudicated

The requested privacy-preserving collections were received on 31 August 2026,
their source manifests verified, and their approved contents imported under
`paper/evidence/laptop/`. The repository and workstation records support the technical history from the
first standalone commit on 2 June 2026 onward.  The workstation's native
AgentsView reports cover KM usage from 11 July onward, and the separate
privacy-preserving coordinator ledger provides hash-bound task evidence from
16 July onward.  Those intervals do not need to be copied from the laptop.
A first-prompt transcript was not retained, so the paper does not claim its
wording or exact conception time. The following list records the original
request and the disposition of each item:

1. The first conversation or prompt in which the reasoner was proposed or
   named, including its timestamp and model/tool identity.
2. The pre-standalone git history or files from
   `~/Documents/papers/neuro-symbolic-independence/` that contain the first KM
   implementation, design notes, or imported Sequoia code.
3. Codex project memory files for KM predating 2 June 2026, especially the
   original architecture, audit, correctness, hybrid-tableau, nominal-routing,
   EL-completion, and Rust-frontend memories mentioned in `AGENTS.md`.
4. Session transcripts or exported conversation histories that show the human
   role in setting objectives, rejecting claims, choosing benchmarks, and
   requiring Lean certification. Full account exports are unnecessary if the
   relevant KM conversations can be exported individually.
5. Any contemporaneous notes explaining why Rust, Sequoia's calculus, the ORE
   2015 corpus, and Lean 4 were selected.
6. An AgentsView export for the KM project over any retained laptop records
   before 11 July 2026, whether AgentsView was already active or is run
   retrospectively.  Use a fixed date range and project filter and provide the native JSON from
   `agentsview usage daily --all --json`, `agentsview stats --format json`, and
   `agentsview activity report --json`, plus the AgentsView version and the
   effective configuration with credentials and unrelated paths removed.  The
   required fields are session and subagent identifiers, model identifiers,
   timestamps, token and cache counters, cost assumptions, tool-call types,
   duration and active/idle measures, peak concurrency, agent-minutes, and task
   outcomes.  A copy of the project-filtered SQLite archive is useful but not
   required.  Prompt and response bodies should be omitted or irreversibly
   hashed.  Record observation start/end times so totals can be reconciled with
   the pinned workstation reports without double counting.  The interval before
   the first standalone commit on 2 June is the highest priority.

The most useful concrete paths or exports are:

- a git bundle made from
  `~/Documents/papers/neuro-symbolic-independence/.git`, including all refs,
  plus the pre-standalone KM files from that working tree;
- the KM entries under `~/.Codex/projects/*/memory/`, especially files whose
  names begin `project_km_` and the `feedback_no_heavy_laptop` record;
- KM-specific session records under `~/.Codex/projects/` and
  `~/.claude/projects/`, preserving original timestamps;
- any individually exported ChatGPT, Codex, or Claude conversations whose
  titles or contents mention Kobayashi-MaRust, KM, Sequoia, ORE, Lean,
  Konclude, or the reasoner project; and
- dated files under the original paper project's notes or results directories
  from before 2 June 2026.

For git history, a `git bundle create km-prehistory.bundle --all` made inside
the original repository is preferable to copying a live `.git` directory.
For memories and sessions, preserve relative paths and modification times but
exclude credential, account, and unrelated-project files.

Preferred delivery is a single directory preserving timestamps, with a short
README mapping each file to its source application. Secrets, credentials,
unrelated conversations, and machine identifiers should be removed before
transfer. The paper will quote no private transcript without explicit approval.

The repository includes `paper/scripts/collect_laptop_history.sh` to make the
first pass reproducible.  Run it on the laptop as:

```bash
bash paper/scripts/collect_laptop_history.sh ~/km-paper-laptop-evidence
```

The script creates a git bundle, copies only the explicitly named KM memory
records, inventories candidate session and untracked worktree files without
copying their contents, and writes SHA-256 hashes.  It deliberately excludes
raw conversations, SQLite archives, credentials, and build artifacts.  Review
the inventory and add only the individually approved KM conversations or
prehistory files before transfer.  AgentsView JSON remains a separate export
because its project identity and available command flags must be checked on
the laptop before querying.
Verify the collection from its own root with
`(cd ~/km-paper-laptop-evidence && sha256sum -c SHA256SUMS)`.

After reviewing the laptop AgentsView configuration and syncing only the
intended KM session roots, collect the non-overlapping native aggregate as a
separate directory:

```bash
bash paper/scripts/collect_laptop_agentsview.sh \
  ~/km-paper-laptop-agentsview kobayashi_marust 2026-06-02 2026-07-11
```

This command never runs `agentsview sync`; all three reports use the existing
frozen database. Its default half-open window ends where the workstation
evidence begins. Review the reported project identity and JSON before
transfer. If the first observed KM activity predates 2 June, rerun into a new
directory with the earlier date and report that boundary explicitly.

## Restricted or credential-gated benchmark inputs

Two inputs cannot be acquired from public unauthenticated endpoints:

1. Expose a BioPortal API key to the acquisition job as
   `BIOPORTAL_API_KEY`. Do not place it in a file under the repository. The
   snapshot script will record submission identifiers and payload digests but
   never the key.
2. Supply a current licensed SNOMED CT International Edition OWL or RF2
   release under the IBEX paper benchmark root. Include the release identifier
   and original archive digest. The artifact will be benchmarked in place and
   excluded from redistribution.

Until these are supplied, the corpus manifests retain explicit
`not_acquired` rows and the paper must not claim complete BioPortal or SNOMED
coverage.
