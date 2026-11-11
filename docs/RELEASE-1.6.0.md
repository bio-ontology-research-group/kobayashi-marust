# KM 1.6.0 release notes

Released 2026-11-12 from commit 45543658 (tag `v1.6.0`).

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
fixture whose first frontend pass carries individual constants. With every
production route forced to decline, the stage publishes 378 of those 592
within its budget and never disagrees with the production answer (0 of
1,781 suite inputs). The practical limit is the dense `named × named`
answer matrix of the Lean answer type, which exceeds memory above about
20,000 classes; a sparse answer type is the first post-release item.

## Speed and correctness (Ibex, same day)

| | v1.6.0 | v1.5.3 same day | Konclude same day |
|---|---:|---:|---:|
| held-out inputs verified (of 585) | 577 | 560 | 575 |
| mean wall-time ratio against v1.5.3 (bound 1.10) | 0.735 | 1 | |
| median wall-time ratio against v1.5.3 (bound 1.10) | 1.026 | 1 | |
| median wall time on the 574 inputs v1.6.0 and Konclude both verify | 0.166 s | | 0.188 s |

No wrong answer on the held-out half or on the 1,708-input pool (1,685
verified; v1.5.3 1,662). The held-out median is after a protocol recheck of
the inputs that ran on four slow Ibex nodes (first pass 1.413; details in
`docs/V1.6.0-ACCEPTANCE.md`).

## Certification

Run on Ibex from the tag because the workstation was out of disk and
memory (`tools/release/v160-ibex/`, asset `certification-ibex.json`): PGO
build (22 of 22 training answers verified), five Lean gates (634 tests, no
`sorryAx`), full Rust suite (95 cargo commands, 3,610 passed, 0 failed),
Java plugin (76 tests), checker step (57 checker tests; checkers-on suite,
0 rejected, 0 answers changed).

## Assets

`km-v1.6.0-linux-x86_64` (PGO, GLIBC at most 2.34), `km-v1.6.0-certified-source.tar.gz`,
`kobayashi-marust-protege-1.6.0.jar`, `BENCHMARKS.md`, `build-completion.json`
(S1 and C1 `met`; L1 and R1 read the workstation receipt layout and show
`pending`; their evidence is `certification-ibex.json`),
`certification-ibex.json`, `SHA256SUMS`.

## Records

`docs/V1.6.0-COMPLETENESS-PLAN.md` (the theorem and the plan),
`docs/V1.6.0-STATUS.md` (the campaign log), `docs/V1.6.0-ACCEPTANCE.md`,
`docs/CERTIFICATION-ROADMAP.md` (the boundary), `lean/README.md`,
`results/agents/2026-11-09/` and `results/agents/2026-11-10/` (agent
reports and measurements).
