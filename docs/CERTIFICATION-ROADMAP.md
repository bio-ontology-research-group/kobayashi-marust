# Certification roadmap

This plan was recorded on 2026-10-27, after the v1.5.4 audit of the Lean
boundary. The audit report is reproduced in
`docs/history/LEAN-BOUNDARY-AUDIT-2026-10-27.md`.

## What the Lean development proves at v1.5.3/v1.5.4

- Each certification gate proves one thing: if a Lean checker accepts a
  certificate document, the answer in that document is exact for the
  normalised clause set it contains.
- The frontend is not modelled in Lean. This covers OWL parsing, IRI
  identity, normalisation, and the role-chain and transitivity encodings.
- Completeness of the EL, CB, and hypertableau procedures is assumed, not
  proved. So is the completeness of automatic routing: the
  `selectedComplete` and `fallbackComplete` fields of `ConcreteSupervisor`
  are assumptions, and the structure is never instantiated. (Changed in
  v1.6.0; see below.)
- No checker runs on the default `km classify` route.
- The Konclude bridge and the incremental-source path have no Lean model.

## Rule route (2026-10-30, v1.5.5)

The rule worker (`KM_RULES_CONSISTENCY`, `KM_RULES_CLASSIFY`) has a Lean
checker for its answers: `rules-cert-check`, theorem
`WireRulesCertificate.check_sound` (docs/DL-SAFE-RULES.md, "Lean
coverage"). An accepted certificate makes the published consistency flag,
unsatisfiable queries and subsumptions between queries exact under the
DL-safe semantics of the decoded clause list, relative to the premises it
lists (the CB entailments the completion schedule takes as given). Outside
the boundary: the frontend (parsing, normalisation, the guarded encoding,
finite-rule grounding of built-ins over asserted literals, the inert-sort
release, which has its own certificate), composition with the CB
certificates of the premises, and completeness of the rule tableau (an
answer without a certificate is refused, not proved wrong). The checker is
off by default (`KM_RULES_LEAN_CERT`, `KM_RULES_LEAN_CHECKER`); the gate is
`lean/run-rules-certification-gate.sh`.

## Plan

| Release | Goal |
|---|---|
| v1.5.5 | Run a test suite with the existing Lean checkers on by default, and record which published answers they accept, reject, or cannot check. |
| v1.5.6 | Prove the frontend in Lean. A theorem must connect the clause set to the source ontology under the OWL 2 direct semantics, covering IRI identity, normalisation, and the regular role-inclusion encoding. |
| v1.6.0 | Prove completeness. Replace the assumed completeness fields with proofs for each procedure on its fragment, instantiate the supervisor, and cover the routing to those procedures. |

## v1.6.0 completeness (2026-11-09 to 2026-11-10)

The assumed fields are gone. `KMAutomaticSupervisor.CertifiedSupervisor`
and `KMConcreteAutomaticSupervisor.ConcreteSupervisor` have no completeness
fields; coverage is the predicate `CoversAt` (one route of the execution
plan publishes at the source), soundness is unconditional, and the
completeness theorems take coverage as a hypothesis. The instance
`KMSupervisorInstance.kmSupervisor rust decide` runs, on every route, the
Rust execution and then two Lean reference procedures:

- the EL reference (`ELReferenceSaturation`, `ELCommonSourceRecognizer`):
  an executable fixpoint of the NF1 to NF7 completion closure over the
  requested names and the ontology's concepts, proved closed and sound,
  behind a recogniser that reads the common clause source as pure EL
  (including the frontend's role-domain and binary-disjointness shapes);
- the ALC reference (`ALCReferenceSaturation`, `ALCCommonSourceRecognizer`):
  the computable finite type elimination of `CompletenessStrategy`, exact
  by `saturate_decides`, behind a recogniser inverting `CBALCEncoding.encode`
  (disjunctive GCIs, existential and universal restrictions, no role
  axioms).

Theorems, all with axioms `[propext, Classical.choice, Quot.sound]`:
`kmSupervisor_sound` (every published answer is exact, for every source),
`kmSupervisor_complete_on_EL`, `kmSupervisor_complete_on_ALC` and
`kmSupervisor_complete_on_EL_or_ALC` (every source the EL or ALC recogniser
accepts, with a duplicate-free request, receives an exact answer), for
every fail-closed Rust executor and every router decision. Routing is
covered without any claim that Rust's profile predicates match Lean's
selector: the theorem holds for every decision.

What this does and does not say:

- It is completeness of the idealised procedure. The reference closures
  have no resource bound; a process running them can time out, which the
  fail-closed design turns into no answer. The release claim is "sound,
  and complete up to resource exhaustion, on the recognised EL and ALC
  fragments of the common clause source".
- The fragments are defined on the frontend's normalised clause stream.
  The frontend itself stays outside the boundary (v1.5.6 row).
- Role hierarchies, inverses, chains, nominals, cardinalities, data and
  rules remain outside the proved fragments. The hypertableau totality
  theorems are relative to a producer that nothing constructs executably;
  the CB completeness chain is conditional on supplied terminal data and
  has no executable saturation or termination theorem. See
  `docs/V1.6.0-COMPLETENESS-PLAN.md` and
  `docs/history/SURVEY-HT-CB-COMPLETENESS-2026-11-09.md`.
- The shipped system realises the theorem only once the Rust supervisor
  runs the reference stage after its exact routes decline
  (`km-el-reference`; acceptance clause P3 of `docs/V1.6.0-ACCEPTANCE.md`).

## v1.5.5 checkers-on suite (2026-10-30)

`KM_LEAN_CHECKERS=<dir>` turns on the applicable Lean checkers in
`km classify` and fails closed on a rejection; `tools/checkers-on-suite.sh`
records, per input, which published answers the checkers accept, reject,
or cannot check. The inventory of checkers, the exactness argument and the
results are in `docs/CHECKERS-ON.md`; the raw results are in
`results/agents/2026-10-30/checkers-on-suite/`.
