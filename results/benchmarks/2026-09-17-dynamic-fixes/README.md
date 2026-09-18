# ABox fixes found by the dynamic benchmarks

Status: experimental fixes pass focused controls, the full 592-ontology ORE
regression, and all four Lean certification gates. Final versioned release
benchmark measurements remain pending. Both versioned binaries pass their
exact-binary corpus audits and all four source certification gates.

The v1.4.0 incremental source API discarded the frontend's ABox inconsistency
verdict. A source containing `DisjointClasses(A B)`, `A(a)` and `B(a)` therefore
returned consistent. The candidate preserves that verdict and suppresses stale
taxonomy rows on the inconsistent revision. Removing the conflicting assertion
restores the original consistent result.

Automatic batch classification had a related admission error. It projected
atomic assertions into independent named-class satisfiability queries without
checking whether one individual had several asserted classes. The candidate
requires one distinct class per individual. Inputs outside that contract use
the existing full ABox path. With multiple classes, ambiguous individual IRI
spellings also decline the shortcut. The single-class case retains its cheap
shared-witness path.

## Experimental evidence

The baseline source regression fails at the consistency assertion. The candidate
passes all 19 incremental source unit tests in the release profile, and all 179
frontend tests in the development profile after correcting an old optimization
test's fixture to satisfy the new admission condition. The general library
suite passes 2,407 tests, with eight ignored and the 22 CI-listed native-checker
tests deferred to the certification gates.

Candidate build `51982442` has source archive SHA-256
`9a77671d75ed4d72e5cf4786610da1daeedb4054058e9b7c13177d10e691204d`
and binary SHA-256
`b51533172b0dfe0def6fb10a8ae15146d5ae95462002cd1ac1289d11cbbd4ac9`.
It is an experimental binary still carrying version 1.4.0, not a release asset.

- Incremental controls `51982564`: all 12 arms match the full canonical output
  of independently agreeing fresh HermiT and JFact runs. See
  [validation](incremental-controls/validation.json).
- Justification controls `51982551`, audit `51982553`: all 30 native/common KM
  cases pass independent HermiT entailment and deletion-minimality checks.
  Evidence is in the sibling dynamic-baseline `candidate-justification` folder.
- [Public API verifier](verify_abox_fix.py): the baseline passes 13 of 19 checks;
  the candidate passes 18. The remaining case is unchanged: the explicitly
  selected manual route rejects a duplicate class assertion with exit code 3.
  Default automatic classification and incremental source controls all pass.

The ORE experiment `51982555` and strict comparison audit `51982569` completed.
All 592 ontologies completed with no semantic differences from the released
baseline: 588 match retained gold, two retain the known consistency mismatch,
and two have no retained gold. See [summary](experimental-ore/summary.json) and
[per-ontology results](experimental-ore/per-ontology.tsv).

After the focused experimental passes, the Lean atomic-ABox publication module
proved 12 theorems. The full routing gate passed 77 test executions, axiom audits,
and valid/forged certificate controls. Its [receipt](../2026-09-17-dynamic-baseline/abox-lean-certification.json)
binds the checked sources. [Certification boundaries](../../../lean/ATOMIC-ABOX-PUBLICATION.md)
state the parser, identity and detector assumptions; this is not a proof extracted
from the Rust implementation.

The remaining native gates also passed: ELC 6, HT 56 and CB 21 test executions.
All 22 native-checker tests excluded from the general suite were observed
passing by exact test name. The [native-gate receipt](../2026-09-17-dynamic-baseline/v141-native-gates-source-manifest.json)
binds the unchanged sources and archived logs. Together with routing, these
cover all four required certification gates on the candidate source.

The versioned v1.4.1 RC1 build `51983011` completed with binary SHA-256
`680d9002583468e7c68115bf67cb60b89e420339db4c6aa22b5ca802206c8629`.
All 308 files in its source archive match the current task worktree; see
[source equivalence](v141-source-archive-equivalence.json). Its
[general release suite](v141-general-release-tests.json) passed 2,407 library
and 59 integration tests; eight
library tests are ignored and 22 native-checker tests are assigned to the gates.
Its public API controls reproduce the candidate's 18/19 result, including the
unchanged manual-route limitation above. Its separate ORE sweep `51983366` and
audit `51983409` completed: all 592 inputs finish with no semantic differences
from the released baseline. See [versioned summary](v141-ore/summary.json) and
[per-ontology results](v141-ore/per-ontology.tsv). Final measured benchmark runs must
identify their exact versioned binary; the experimental binary is not a release
asset.

The exact v1.4.2 RC1 binary `705cac1500018d18018ca4d5482a7451e836091b26648453824afa4b36d16fdb`
also passes its own 592-ontology sweep `51983958` and audit `51983967`, with
no semantic differences from the released baseline. Its
[summary](v142-ore/summary.json) and [per-ontology results](v142-ore/per-ontology.tsv)
preserve the same 588 gold matches, two known consistency mismatches and two
inputs without retained gold. Final benchmark comparisons remain separate.

## Plugin release metadata and interface checks

The plugin's OWLAPI `getReasonerVersion()` still returned 0.3.0. The release
candidates update that metadata to 1.4.1 and 1.4.2 respectively, matching their
package and OSGi bundle versions. This changes no classification, update or
explanation behavior. The test consumer now checks the reported API version
against the installed bundle in the real Protégé runtime.

Both versioned plugins pass 31 Maven tests with zero failures or skips, packaged
OSGi verification, and an isolated stock Protégé 5.6.6 smoke covering native
classification, retained incremental addition and a two-source-axiom
explanation. The [plugin receipt](../2026-09-17-dynamic-baseline/plugin-validation.json)
binds the final JARs, source metadata and exact benchmark binaries. Superseded
JARs and their original receipts remain in the local evidence archive.
The Lean proof boundaries concern reasoning and answer publication; the plugin
version string is separately validated package metadata.

The exact 1.4.2 Cargo source independently passed all four certification gates
(ELC 6, HT 56, CB 21, routing 77 test executions), with all 22 excluded native
checker test names observed passing and unchanged source hashes. See the
[1.4.2 gate receipt](../2026-09-17-dynamic-baseline/v142-native-gates-source-manifest.json).
Its general release suite also passed 2,407 library and 59 integration tests,
with eight ignored library tests and the 22 native checks covered by the gates.
