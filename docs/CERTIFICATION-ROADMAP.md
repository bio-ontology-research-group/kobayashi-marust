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
  are assumptions, and the structure is never instantiated.
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
