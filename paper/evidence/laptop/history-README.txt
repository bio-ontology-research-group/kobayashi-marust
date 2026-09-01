KM laptop-history evidence
collection_utc=2026-08-31T15:36:12Z
cutoff_utc=2026-06-02T00:00:00Z
original_repository=/home/leechuck/Documents/papers/neuro-symbolic-independence

This collection intentionally omits credentials and raw agent sessions.
The git bundle and named KM memory files are substantive evidence.
The session inventory contains only path, timestamp, size, and SHA-256.
Review every file before transfer. Do not add credentials or unrelated conversations.

Collector deviations and findings (recorded 2026-08-31, collection operator):

1. memory/: the laptop has no ~/.Codex/projects or ~/.codex/projects tree,
   and the Codex memories_1.sqlite database is empty. The KM project memory
   records anticipated by evidence-needed.md live under Claude Code's
   per-project auto-memory instead:
     .claude/projects/-home-leechuck-Documents-papers-neuro-symbolic-independence/memory/
       (pre-standalone root: project_km_audit, project_km_correctness_audit,
        project_km_hybrid_tableau, project_km_nominals_routing,
        project_km_el_routing, project_km_rust_elc, project_km_sroiq_program,
        project_km_reasoner_benchmark, project_rust_frontend,
        feedback_no_heavy_laptop, and others)
     .claude/projects/-home-leechuck-Public-software-kobayashi-marust/memory/
       (standalone-era root)
   All project_km_*, feedback_no_heavy_laptop*, and project_rust_frontend.md
   files from both roots were copied under memory/ with original relative
   paths and modification times (76 files). Modification times reflect the
   last update, not creation; creation predates or accompanies the covered
   work.
2. inventories/km-session-candidates-codex-sessions.tsv: supplementary
   inventory added because the laptop Codex layout stores transcripts under
   ~/.codex/sessions/YYYY/MM/DD/ (not ~/.codex/projects), which the original
   script does not scan. Same columns and matching rules; 440 candidate
   files. Contents were not copied.
3. Observed boundaries: earliest KM-mentioning Claude session artifact is
   2026-06-02; earliest AgentsView-recorded session in the originating
   neuro_symbolic_independence project is 2026-05-15. See the separate
   km-paper-laptop-agentsview collection for the aggregate export and its
   boundary report.
