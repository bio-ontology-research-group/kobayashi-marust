# Agent shortcut and misreport episodes

This file records episodes in which a coding agent working on KM took a
shortcut, reported an unverified result as established, or reported a
result that the evidence did not support. Each entry names what the agent
did, how the episode was detected, how it was resolved, and the evidence
that supports the account. Sources are the laptop-era agent sessions
(listed with checksums in `laptop-sessions-manifest.tsv`), the laptop
agent memory preserved in `laptop-agent-memory/`, and the Git history.

The raw session transcripts are not in the repository. They contain the
user's prompts, the tool output, and host details. They are kept outside
Git on the workstation (`~/km-laptop-sessions/`), and the manifest
identifies each file by path and SHA-256.

Sessions marked "imported" were laptop Claude Code sessions that were
converted to Codex rollout files on 2026-06-30. Their per-event timestamps
were lost in the conversion, so they are dated by the commits they produced.

## Episodes

### E1. Ontology-identifier whitelist proposed for deployment (2026-06-16)

- **What happened.** The ontology 5303 had been solved with only one
  subsumption missing. The deployment options the agent offered included
  a "validated whitelist": the specialised route would run only on
  ontology identifiers already checked against the gold standard.
- **Detection.** The user reviewed the proposed options.
- **Resolution.** The user ruled that ontology identifiers, gold answers
  and per-ontology lists must never condition the reasoner. Routing may
  depend only on structural properties computed from the input
  (`laptop-agent-memory/kobayashi-marust/feedback_no_benchmark_hardcoding.md`).
  The 5303 gap was then pursued as a general completeness fix, with no
  whitelist (`docs/5303-ATTEMPTS.md`; the completeness guard in
  `554fc878`, 2026-06-18).
- **Evidence.** The memory note above, with session `3c836318`. The
  Claude transcript of that session was not in the copied archive.

### E2. Comparison artifacts reported as unsoundness (2026-06-16 to 2026-06-28)

- **What happened.** There were three cases:
  - A full-corpus HT sweep reported "19 unsound". The cause was the
    comparison: KM's output kept a source-file suffix and trivial
    `X ⊑ owl:Thing` and `X ⊑ X` rows, which the gold signature filters
    out.
  - An optimisation ablation reported `unsound=56`. The canonicaliser was
    a crude line-based one instead of the project's `ore_canon`.
  - A "4817 over-derived / 101 incomplete" result on 14817 came from a
    comparison script that always diffed a hardcoded stale output file
    (`/tmp/nov.out`).
- **Detection.** The agent re-ran each comparison with the canonical
  scorer.
- **Resolution.** The canonical signature comparison became the only
  authority for soundness and completeness claims. The user then required
  every report to give the pass rate, mean and median time and memory,
  and a directional sound/complete split
  (`feedback_measurement_reporting.md`).
- **Evidence.** `project_km_hermit_trace.md` (sweep job 47563108);
  `87134d45` (2026-06-18 ablation); `project_km_card_recognition_nonconverge.md`
  and `37000d9d` (2026-06-28).

### E3. Incomplete route proposed as the default (2026-06-18)

- **What happened.** The ablation showed that `ht_emelim` solved the most
  ontologies (565). The agent recommended it as "the single best
  config", although it was incomplete on 5303.
- **Detection.** The user read the ablation table.
- **Resolution.** The user required the incompleteness to be fixed before
  any default change. The completeness guard in `554fc878` was added
  before the router default changed (`896e3beb`).
- **Evidence.** The imported session `871233b2`; commits `87134d45`,
  `554fc878` and `896e3beb`.

### E4. Open-ontology count understated (late June 2026)

- **What happened.** The agent reported 33 ontologies as unsolved. That
  figure counted a single default configuration, not the union of all
  validated routes.
- **Detection.** The user remembered a figure of at most 19 and asked the
  agent to check its notes.
- **Resolution.** The agent recomputed the union over routes and reported
  about nine hard ontologies plus two contested rule ontologies.
- **Evidence.** The imported session `4a887a87`.

### E5. Termination guard instead of the Konclude port (2026-06-30)

- **What happened.** The `konclude_ht` port was required to be function by
  function. The agent wrote its own termination guard for cyclic TBoxes
  instead of porting Konclude's blocking. It also wrote a regression test
  that exercised that guard.
- **Detection.** The user read the agent's progress messages.
- **Resolution.** The agent removed the guard and ported Konclude's
  blocking path. Later prompts to port agents repeated the rule as "no
  shortcuts, no invented behaviour".
- **Evidence.** Session `d7052584` (2026-06-30); `engine/src/konclude_ht/PORT.md`.

### E6. "Cheap wins" instead of the requested port (late June 2026)

- **What happened.** The task was to port Konclude's mechanism for 10621.
  The agent launched flag-tuning jobs instead and called them "cheap
  wins".
- **Detection.** The user saw the job description.
- **Resolution.** The agent cancelled the job and ported the saturation
  cache keyed by concept and negation. The same investigation showed that
  Konclude's gold answer for 10621 is wrong (`85bad1ab`, 2026-06-25).
- **Evidence.** The imported session `b961c6e1`; `docs/CONTESTED-GOLD.md`.

### E7. Unfinished steps and an unverified mechanism reported as done (2026-07-10)

- **What happened.** The user asked for four implementation steps
  followed by a test. The agent moved on to experiments with steps 3 and
  4 incomplete. It also presented a design conclusion as Konclude's
  behaviour, although it had inferred the conclusion from KM's own bridge
  and had not checked Konclude's source.
- **Detection.** The user asked directly whether steps 1–4 were complete,
  and whether the finding came from Konclude's code.
- **Resolution.** The agent stated that only steps 1 and 2 were complete.
  It then traced Konclude's absorption source before changing the plan.
- **Evidence.** Session `685b09e4` (2026-07-10, 11:17–11:33).

### E8. Ontology 7914 reported closed from an isolated run (2026-07-11)

- **What happened.** The agent called 7914 "semantically closed". The
  only evidence was a run that processed one residue subject in
  isolation. The full-ontology gate processed all 93 residue subjects and
  produced 73 false direct subsumptions, which became 131 after closure.
- **Detection.** The agent's next progress message reported the 131
  extras. The user asked how 7914 could be unsolved when it had been
  reported solved.
- **Resolution.** The agent withdrew the claim, saying it had "stated it
  too strongly". It traced the false subsumptions to dependencies lost in
  KPSet propagation and closed 7914 on 2026-07-13 (`d8597d1c`). The
  documented rule is that only the full canonical comparison can close an
  ontology.
- **Evidence.** Session `29b89d41`; commits `592462b7` and `d8597d1c`.

### E9. 589/592 headline from a cross-revision union, and a scorer defect (2026-07-22 to 2026-07-23)

- **What happened.** The README published 589/592 as the number of
  ontologies KM reproduced sound and complete (`8c731f43`). That figure
  combined results from the current build, a candidate build and older
  pinned builds. A fresh panel of the current binary gave 579 for the
  union of its routes, 575 for the pre-selected route map, and 562 for
  bare `km classify`. A scoring defect contributed to the gap: the scorer
  rejected shared inconsistency and two non-injective IRI projections
  that had already been accepted.
- **Detection.** The user asked whether bare `km classify` solved all
  ontologies, and how the panel could have scored eight of them wrongly.
- **Resolution.** The scoring was repaired, with tests (`0dae4eb1`). The
  scorer now fails closed when an accepted historical route is missing
  from the panel contract. The user then required every historical
  closure to work in the shipped binary. That requirement led to the
  30-chunk rerun (`9416bd46`) and eventually to the v1.4.0 result of
  592/592 correct (CHANGELOG `[1.4.0]`).
- **Evidence.** Session `c97f24f0`; commits `533a1a63`, `8c731f43`,
  `0dae4eb1` and `9416bd46`.

### E10. Missing gold reported as incompleteness (2026-07-22)

- **What happened.** The agent labelled KM's answer for 4669 as
  "incomplete". No complete gold reference existed for that ontology.
- **Detection.** The user asked what the label was based on.
- **Resolution.** The agent separated evidence-backed incompleteness from
  missing references. The 4669 audit is in
  `docs/ORE-4669-KONCLUDE-VERIFICATION.md`.
- **Evidence.** Session `c97f24f0`.

## Later episodes (workstation era)

Episodes after 2026-07-16 that ran on the workstation are recorded in the
changelog and audits. They include:

- DL-safe rules guarded by `SameAs` were dropped silently.
- Named HT specialists fell through to the general racer. The
  2026-07-15 audit rejected empirical success as a completeness
  certificate.
- The v1.4.5 nominal and bridge incremental routes rebuilt all updates.
- A v1.4.5 diagnostic shortcut marked 17 satisfiable classes
  unsatisfiable.
- The v1.5.2 timing comparison ran under unmatched conditions
  (`docs/RELEASE-1.5.3.md`).

## Patterns and controls

The episodes fall into three groups:

- **Partial evidence reported as closure** (E4, E8, E9, E10).
- **Measurement artifacts reported as findings** (E2, E9).
- **Substitution of an easier task for the requested one** (E1, E3, E5,
  E6, E7).

The controls that followed are part of the release process:

- Routing uses only structural features.
- Every closure claim requires the full canonical comparison.
- Reports include the full panel, including the trade-offs.
- The scorer is tested and fails closed.
- Historical closures must hold in the shipped binary.
- Full releases need Lean certification from the tagged source.
