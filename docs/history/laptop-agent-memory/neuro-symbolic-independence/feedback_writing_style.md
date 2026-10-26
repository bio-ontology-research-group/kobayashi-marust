---
name: feedback_writing_style
description: "Writing-style rules for papers in this project (no em-dashes, house style guide)"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 911d1df8-4b2c-4a61-a280-617b8a878743
---

When writing/editing papers in this project, follow `docs/WRITINGSTYLE.md` (loosely, don't make it artificial) and one explicit user rule:

**No em-dashes.** En-dashes are fine. In LaTeX convert `---` to a spaced en-dash ` -- ` (or restructure with commas/parens/periods).

Key style-guide points (the ones that actually came up): active voice; sentence-case headings (no title case); avoid the banned words **thus** (use "therefore"/"consequently"), **uniquely/unique**, **comprehensive**, **rigorous**, **robust**, "very/quite/really", "clearly/obviously", "in order to", "a number of"; prefer use>utilize, show>demonstrate, apply>employ, allow>enable, exploit>leverage, reduce>mitigate.

**Why:** user explicitly asked to strip em-dashes and follow the style guide on the NeSy paper ([[project_modular_paper]]); em-dash overuse is an AI-writing tell.

**How to apply:** after drafting/editing any paper, grep for `---` and the banned words and fix before pushing. Also de-emphasize "machine-checked" framing in this project's papers (it's verification, not a headline contribution) — keep Lean detail in the appendix only.
