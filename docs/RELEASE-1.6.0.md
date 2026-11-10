# KM 1.6.0 release notes (draft)

Status: draft on `development/v1.6.0`; the release date, commit, speed
table and acceptance evidence are filled in when the tag is cut.

## What this release proves

KM 1.6.0 replaces the assumed completeness of the automatic supervisor by
a theorem. Up to 1.5.5 the Lean routing capstone took two fields,
`selectedComplete` and `fallbackComplete`, as hypotheses, and no
instance of the supervisor existed. Those fields are gone. The supervisor
is instantiated (`KMSupervisorInstance.kmSupervisor`), for every
fail-closed Rust executor and every router decision, with two executable
Lean reference procedures running after the production workers decline:

- the EL reference (NF1 to NF7 completion closure over the requested names
  and the ontology's concepts, proved closed and sound), behind a
  recogniser that reads the common clause source as pure EL, including
  n-ary conjunctions, role domains and disjointness as the frontend emits
  them;
- the ALC reference (computable finite type elimination, exact by
  `CompletenessStrategy.saturate_decides`), behind a recogniser inverting
  `CBALCEncoding.encode`: disjunctive GCIs, existential and universal
  restrictions, no role axioms.

Theorems, all with axioms `[propext, Classical.choice, Quot.sound]`:

| theorem | statement |
|---|---|
| `kmSupervisor_sound` | every published answer is exact, for every source |
| `kmSupervisor_complete_on_EL` | every recognised EL source with a duplicate-free request receives an exact answer |
| `kmSupervisor_complete_on_ALC` | the same for recognised ALC sources |
| `kmSupervisor_complete_on_EL_or_ALC` | the union |

The claim, stated exactly: sound for every published answer; complete,
up to resource exhaustion of the reference procedures, on the EL and ALC
fragments of the frontend's normalised clause stream, whichever route the
selector and its fallback chose. The frontend (parsing, IRI identity,
normalisation) stays outside the boundary. Role hierarchies, inverses,
chains, nominals, cardinalities, data and rules remain unproved for
completeness; the status of the hypertableau and CB chains is recorded in
`docs/history/SURVEY-HT-CB-COMPLETENESS-2026-11-09.md`.

## What the shipped binary does

`km classify` on the automatic route runs a reference stage after the
selected route and its exact fallback have both declined
(`KM_REFERENCE_STAGE=0` turns it off). The stage reruns the frontend,
hands the clause stream and the requested names to the Lean executable
`km-el-reference`, which recognises, saturates, rechecks its own answer
with the Lean acceptance predicate and prints the matrix; the Rust side
only parses. The ALC reference runs in the same binary after the EL one,
under a signature budget (`KM_ALC_REFERENCE_MAX_CONCEPTS`, default 16),
because type elimination is exponential; a budget refusal is a decline,
never an answer. `KM_REFERENCE_FORCE=1` makes every production route
decline so the stage can be exercised.

Fragment measurement on the 593 `elc`-routed inputs of the checkers-on
suite: 592 recognised (all 585 ORE inputs); the one rejection is a rule
fixture whose first frontend pass carries individual constants. The
recogniser runs in 0.17 s median and 32 s at most (2.9 million clauses).

## Acceptance

(filled in at release: P1 to P5 of `docs/V1.6.0-ACCEPTANCE.md`, the
forced-decline suite run, the Ibex speed and coverage clauses against
1.5.3 and Konclude, the five gates, Rust, Java, checkers-on suite.)

## Records

`docs/V1.6.0-COMPLETENESS-PLAN.md` (the theorem and the plan),
`docs/V1.6.0-STATUS.md` (the campaign log), `docs/V1.6.0-ACCEPTANCE.md`,
`docs/CERTIFICATION-ROADMAP.md` (the boundary), `lean/README.md`,
`results/agents/2026-11-09/` and `results/agents/2026-11-10/` (agent
reports and measurements).
