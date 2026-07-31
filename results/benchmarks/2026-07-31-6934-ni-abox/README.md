# ORE 6934 typed-ABox SHOIQ recovery

This capsule records the feature-gated automatic recovery of
`ore_ont_6934.owl`. The default `km classify` route now selects
`nominal_ni_abox`; the specialist returns a classification only after the
source frontend and converted worker input independently establish their
contracts. The exact nominal CB procedure remains the portfolio fallback.

## Certificate and route

The frontend's positive-data-assertion certificate now handles inherited data
properties and class-conditional maximum/exact cardinality one. It rejects an
unsupported constraint only for data properties whose omission could matter,
recognizes `rdfs:Literal` as the top datatype, and treats
`owl:topDataProperty` as the super-property of every data property. Conservative
source scans reject constraints in uncertain class, domain, range, or malformed
property shapes.

After normalization, complete typed-ABox/data omission lets automatic routing
refine a nominal profile to `NominalNiAbox`. The worker then checks all of the
following before it may publish an answer:

- complete native typed-ABox materialization;
- retained inverse-role information;
- no dropped converted axiom;
- the no-blocking SHOIQ completion certificate;
- exact retention of every inverse-functional RBox fence as the normalized
  equality clause `R(x,z) and R(y,z) -> x=y`.

The converter also accepts an empty internal individual suffix when the proxy
resolves to a valid full IRI, and allocates missing named-class markers only
from the trusted typed ABox. Generated or internal missing markers still make
the worker defer.

These are routing, conversion, and eligibility changes. They do not alter CB
rule premises, conclusions, ordering, redundancy, or the derived calculus
fixpoint, so they require no Lean re-certification.

## Local validation

The complete serial release library suite passed with 1,825 tests, zero
failures, eight intentional ignores. Focused tests cover inherited data
properties, duplicate values, cardinality-one clashes, top datatypes and top
data properties, malformed source shapes, empty-suffix individual IRIs,
trusted ABox-only classes, generated-class rejection, and exact
inverse-functional-clause retention.

## Source-bound IBEX evidence

The workstation executable was not deployed because it requires GLIBC 2.39.
The first four-task attempt, job `49688221`, is therefore quarantined as a
deployment failure and is not benchmark evidence. Build job `49688230` instead
verified source archive
`source-5cfccc5.tar.gz` (`e7fbdfee4b6824e48035b9231f22da0e43d7975f42462120037ea29f19e9c49f`),
built commit `5cfccc5ace25326bee70e48f5187808b9af3f645` on an IBEX Gold 6248 compute
node, and produced cluster executable
`afdc15a00168a23f4426b0ca155f54ad6c3cb65cbad745f07e5f2eef862f0e3a`.

Focused array `49689197` passed all four exact-signature gates:

| Ontology | Result | Wall time | Peak memory |
|---|---:|---:|---:|
| 6934 | exact | 198.212 s | 1,432.32 MiB |
| 10702 | exact | 2.5698 s | 23.39 MiB |
| 15846 | exact | 212.9466 s | 18,925.83 MiB |
| 6999 | exact | 0.3013 s | 94.59 MiB |

The same executable is frozen in the complete v16 automatic sweep, array job
`49689798`, with dependent audit `49689799`. Its production 6934 task selected
`nominal_ni_abox` and matched the gold signature exactly in 199.3235 seconds at
1,434.64 MiB. It returned 449 subsumptions, zero unsatisfiable classes, and a
consistent verdict; signature SHA-256 is
`5e60a794400802833a9d5785abb6320b7b13d702e48a4c810462bad6c1fc931e`.
The original dependent audit `49689799` rejected eight legitimate
`nominals` to `nominal_ni_abox` post-normalization refinements because its route
model treated the source candidate as terminal. It did not find a reasoner
result regression. The corrected generic audit permits this transition only
when the serialized source profile contains the complete structural candidate;
it has no ontology whitelist.

Independent audit job `49692538` then passed all integrity and route checks.
The final 592-row aggregate contains 588 `ok`, two `error`, one `timeout`, and
one `unsupported` result. Full-IRI scoring gives 586 exact matches and the two
adjudicated consistency mismatches 2669 and 15516. There are no missing or
duplicate rows. The corrected auditor SHA-256 is
`074690b2e9f3507048315d27f04e85be4ca69469c003a6c3cda934797877a57c`.

Reproduction scripts in this directory perform the source-bound compute-node
build and focused exactness gate.
