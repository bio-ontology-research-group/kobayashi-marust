# Agent work log for v1.5.4, 2026-10-27 to 2026-10-28

The maintainer's Claude Code session supervised these agents. Until the
evening of 2026-10-28 they were Claude subagents; after that, at the
maintainer's direction, all new work went to the pi coding agent
(`~/.local/bin/pi-opencode`, opencode-go provider, model `kimi-k2.7-code`),
and Claude only briefed, reviewed and merged. Every merged commit is a
cherry-pick onto `development/v1.5.4`; the agents' branches therefore still
show as ahead of it. Nothing was pushed.

The scratch directory these artifacts came from was tmpfs and is not kept.
This directory preserves what is small and reusable.

## Claude subagents

### Protégé bug 1 / object-data sorts agent

Branch `fix/v154-bug1-nominal-cb`. Finished.

1. Diagnosed the bug 1 hang (nominal CB with `owl:topObjectProperty` and data
   values) into three causes. A: the data-value at-most-one clause lay
   outside the calculus normal form. B: x-form facts were seeded into the
   ground context, which is a calculus change and was deferred. C: the object
   and data domains were not separated.
2. Implemented cause A as a fresh-nominal rewrite (`d2bc2f47`). It was later
   reverted (`8a307740`) because it turned ORE 9800 into a timeout. Remedy
   (a), a `D(o_A)` sort fact, did not help; its patch was lost in a /tmp
   cleanup.
3. Implemented the object/data sort encoding (`frontend/sorts.rs`):
   `b574d11e`, then the closure under the clause set (`e054f6b7`) after
   design run 5 exposed three unsound `nominals` answers, then "never widen
   sorts fixed by Direct Semantics" (`7bfc82be`) after a missed
   inconsistency, then pinning individuals through their nominal proxy
   (`a213a058`) after run 7 lost seven inputs.
4. HermiT differential test of the sort encoding: 400 generated seeds. Before
   the fix, 55 of 113 re-run seeds were wrong; after it, 0 new wrong answers
   and 61 timeouts. Its regression fixtures are committed under
   `engine/tests/fixtures/sorts_differential/`. The generator itself was
   deleted during the cleanup.
5. Sibling at-most-one prototype (`V(x,z1) ∧ V(x,z2) ∧ v(z1) ∧ v(z2) → z1 ≈ z2`):
   14 timeouts removed, 3 added. Parked, not committed; its patch was lost.
6. Silent-drop audit (`05d7b0e7`): every non-neutral parser drop is now
   published as DROPPED. The audit table is in the commit's report and
   belongs in the release notes.
7. HasKey as DL-safe rules (`0469edf7`). Two further wrong answers fixed: the
   rule route with nominals (`7fa5ce98`) and a default-route test
   expectation (`ec5837c5`). `generators/gen_haskey.py` is its probe
   generator.

### Datatype agent

Branch `fix/v154-datatype-literal-unsat`. Finished.

1. Empty and universal data ranges, bottom properties and complement
   identities (`4f0cdc54`, `7ca9be96`). The excluded middle for
   `DataComplementOf` (`2ca19da4`).
2. Data-property assertions carried on every clause route (`5a9eaa77`), and
   the profile abstraction above the 512-literal cap (`8491de62`, exactness
   argument in `docs/DATA-ASSERTION-PROFILES.md`).
   `prototypes/bitcode-prototype.diff` is the measured but rejected bit-code
   distinctness encoding: exact, but it does not classify the five
   merge-and-count inputs in time.
3. Found the Sequoia-ordering incompleteness in nominal mode (seed 297) and
   the latent ground-body engine defect. Fixed the loader (`19c221f1`), the
   environment override (`87588a40`) and the gate (`2c8decc0`). Measured the
   cost: `cost/seq-order-gate-times.tsv`. Experimented with dead-disjunct
   encodings, which did not help (recorded in `docs/NOMINALS-CB.md`
   section 7).
4. Found, with a nominal-free ALCHIQ generator, that the automatic route was
   wrong on 34 of 283 seeds: `generators/gen_alc.py`, `sq_run.py`,
   `auto_cat.py`, with seeds and verdicts in `generators/alchiq-seeds/`. This
   led to the bridge agent.
5. Diagnosed the bridge datatype-extension test as a stale expectation and
   prepared `prototypes/bridge-test.patch`, which was handed to pi-opencode.

### Bridge soundness agent

Branch `fix/v154-bridge-soundness`. Finished, all merged.

Fixed three Konclude-port defects, compared against Konclude's C++: the
polarity of negated `≤n` (`0fefad93`), the `≥0` absorption trigger
(`a792590a`), and insufficiency propagation to copy nodes (`5ff91c1a`).
Regression fixtures are in `cd679700`. Result: 0 wrong of 700 seeds, from
70. `bridge/eval.py` is its seed harness; `base*.txt` and `fixD*.txt` hold
the per-seed verdicts before and after; `top10.txt` and `flips.txt` hold the
corpus timing checks.

### Earlier agents (2026-10-26/27)

Realization (`761abca1`–`9385bf29`), universal role (`2179c50c`),
incremental-source bug 4 (`db006fa5`), and the checkers-on suite
(`test/v154-checkers-on`, not for merging). All finished.

## pi-opencode (kimi-k2.7-code)

Briefs are in `pi/*.md`, the session transcript in `pi/sessions/`, and the
first run's log in `pi/issue4-run1.log`.

- **Issue #4 fix** (`issue4.md`). Done and merged as `88c3ff67`: a
  one-function patch of the vendored horned-owl 1.4.0 OFN writer, which
  sliced strings by character count instead of byte index. Reviewed: the
  vendored crate differs from upstream only in that function.
- **Issue #4 follow-up** (`issue4b.md`). Diagnose why QUDT classification
  exceeds 600 s, without code changes. Still running when this log was
  written; its output goes to the scratchpad `pi/issue4/pi2.log`.
- **Bridge test** (`bridgetest.md`). Apply the stale-test patch in worktree
  `.work/worktrees/fix-bridge-literal-test`. Still running when this log was
  written; its output goes to the scratchpad `pi/bridgetest/pi.log`.

## Design-half analysis

`design-analysis/analyse.py` reads the chunk summaries of a paired run (the
v153 policy against the general policy on the same binary). The chunk
summaries of runs 1–7 stay on Ibex under
`/ibex/scratch/projects/c2014/hohndor/km/v154-routing-20261026/paired-design-<array>/chunks/`.
`RUNS.md` lists the array ids.
