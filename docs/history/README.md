# Development history records

This directory keeps records of how KM was developed with coding agents
before work moved to the workstation on 2026-07-16.

- `AGENT-SHORTCUT-EPISODES.md`: episodes in which an agent took a shortcut
  or misreported a result, how each was detected, and the controls that
  followed.
- `laptop-agent-memory/`: the laptop agents' running notes, copied
  unchanged on 2026-10-26.
  - `kobayashi-marust/` holds the notes of the KM checkout
    (2026-06-10 to 2026-07-16).
  - `neuro-symbolic-independence/` holds the KM-related notes from the
    earlier papers tree (to 2026-06-10).
  
  The notes record what the agents believed at the time. Check every
  number in them against the Git history or the release documents before
  you rely on it.
- `laptop-sessions-manifest.tsv`: the 379 laptop agent session files that
  concern KM. Each row gives the file's relative path, its first and last
  event, the working directory, the number of user messages, its size and
  its SHA-256.

The session files themselves (about 1.1 GB) are not committed, because they
contain prompts, tool output and host details. They are kept on the
workstation under `~/km-laptop-sessions/codex/`. The laptop Claude Code
transcripts were not in the copied archive; only their memory notes were.
