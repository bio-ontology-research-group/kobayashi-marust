# Incremental deletion reproof

The opt-in `KM_INCREMENTAL_DELETION_SUPPORT=1` path rederives previously
published positive answers after a pure source-axiom deletion. It retains a
row only when every old answer has fresh support. Deletion cannot create new
entailments, and the old consistent model still satisfies the reduced theory.
Previously unsatisfiable queries require a fresh bottom proof.

The implementation uses source inclusions, equivalences, disjointness,
conjunction, existential monotonicity, and unchanged typed role domains,
chains and transitivity. It does not identify existential expressions with
their fillers. Unsupported expressions, resource bounds or changed source
background decline reuse. Existing source coverage, public IRI ownership and
complete RBox checks remain required. Runtime HT certification disables this
experimental path; it remains off by default.

On ORE9944, the one-axiom deletion rederives all four invalidated rows, leaving
zero subject probes. The 32-axiom deletion rederives 2,103 of 2,180 invalidated
rows, leaving 77 subject probes. The latter module uses 1,034 of 16,538 source
axioms. Across all 8,008 queries, retained rows rise from 5,828 to 7,931.
These counts establish actual reuse, not a release-wide speed claim.

Five deletion tests include exhaustive two-element finite-model deletion
comparisons and guards for additions, missing answers, inconsistency,
unsupported expressions, existential direction, role-chain direction and
invalid role indices. All 26 source-session tests pass with default settings
and with experimental reuse enabled; all 14 typed incremental tests pass.
See `deletion-support-validation.json` for test-log hashes and binary identity.

Two repetitions of five real revisions preserve exactly the fresh answers in
both module and full-input modes. Module reuse beats fresh on 5/8 updates;
full-input reuse wins on 2/8. The large deletion takes 1.594–1.678 seconds
against 1.627–1.676 seconds fresh, winning one repetition and losing the other.
The large addition remains slower at 2.114–2.194 seconds versus 1.649–1.784.
All-case incremental speedup is not achieved. Timings are bounded workstation
diagnostics on one ontology, not the fixed 80-ontology release panel.

`IncrementalDeletionSupport.lean` proves sound support derivations, consistency
preservation, row preservation and query satisfiability conditions. The routing
gate audits its seven theorems. This semantic proof does not yet bind the Rust
source parser, expression graph, IRI map and derived edges to checked runtime
proofs. Passing existing production gates does not close that integration gap.
The certification receipt records exact source hashes and gate outcomes;
`release_approved` remains false.

Next performance work should target the large addition and remaining repeated
frontend/publication work. Promotion requires executable proof binding and the
unchanged complete incremental panel, including every failure and slower case.
