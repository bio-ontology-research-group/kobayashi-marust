---
name: feedback_commit_author
description: "HARD RULE — git commits are authored by Robert Hoehndorf only; never add a Claude author or Co-Authored-By trailer, anywhere"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 3c836318-7e78-4273-b047-e6d829943f1e
---

The author of ALL git commits is **Robert Hoehndorf**, NOT Claude — ever, anywhere.

**Why:** user's explicit, emphatic instruction (2026-06-18). Overrides the
CLAUDE.md convention that says to append `Co-Authored-By: Claude ...`.

**How to apply:** never add `Co-Authored-By: Claude ...` (or any Claude author)
to commit messages or PR bodies in this repo. Commit as the configured git user
(Robert Hoehndorf / robert.hoehndorf@kaust.edu.sa) with a plain message and no
AI-attribution trailer. This supersedes the CLAUDE.md commit-trailer line.
