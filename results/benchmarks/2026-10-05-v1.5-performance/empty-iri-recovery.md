# Source IRI preservation and automatic data-source recovery

ORE 10080 contains the valid individual IRI
`http://code.google.com/p/information-artifact-ontology/`. Taking its empty
local part as its internal identifier caused the native ABox coverage guard to
refuse the otherwise supported source. The registry now allocates a nonempty,
collision-safe identifier and preserves its exact full-IRI owner. The coverage
guard remains unchanged. Tests cover both insertion orders and collisions with
a real source identifier using the replacement spelling.

Automatic ground-source scheduling also excluded this sparse data ABox because
its terminology exceeded the old bound. A bounded attempt now permits at most
4,096 classes and 40,000 logical axioms when there are at most 16 positive data
assertions. Existing file-size, individual-count, import, rule, exact compiler
instance, and native coverage limits remain in force. This scheduling decision
does not certify an incomplete reduction or alter the reasoning rules.

The standard release-profile artifact `09bf32a4e57b` completes ORE 10080 through
automatic routing in 8.85 seconds on one local CPU. Consistency and taxonomy
agree with Konclude, ELK, and Whelk. The previous five automatic data-source
recoveries still agree with Konclude, HermiT, Openllet, and JFact. These bounded
local checks are diagnostics, not full-corpus release performance figures.
The 556-data-assertion ORE 11378 probe still times out at 45 seconds under
explicit ground-source routing; this family is not newly admitted by the
scheduling change.

All four production Lean gates passed for the 778-file source manifest without
`sorryAx`. The configured serial library suite passed 2,708 tests with eight
ignored. Earlier unconfigured/incompletely configured library invocations failed
because required native checker executables and worker paths were absent;
the final invocation configures those executables explicitly.

The local old/new frontend comparison preserves every ordered clause and source
expression after binding the two changed internal names to their original
source owner on ORE 10080. ORE 11378 is byte-identical. Full frozen-corpus
frontend audit **53312770** covers all 1,920 inputs and is pending. Its checker
uses byte hashes directly for unchanged outputs and source-bound renaming for
changed outputs. Audit failures remain failures, not presumed equivalence.
The fix has not yet completed a full classification sweep and is not a release.

The first full-audit snapshot records 261 inputs: 235 successful preservation
checks, including nine with source-bound renaming, and 26 nonzero frontend
outcomes. All 26 are already-adjudicated invalid inputs; the old frontend
refuses them before the successful-output checker can compare both binaries.
This does not yet prove refusal preservation. Supplementary job **53313326**
checks both binaries on the 212 frozen invalid inputs and requires positive
refusal exit codes, an explicit OWL 2 DL admission diagnostic, and identical
stdout, stderr, and metadata. A local ORE 11636 check passes. The original job
and its failure records remain unchanged; the two audits must be reconciled
before declaring the full frontend check complete.

Separately, the earlier nominal-guard full sweep **53303803** has completed:
1,602 verified successes, mean 7.519 seconds, median 0.378 seconds. It still
fails the v1.5.0 target against Konclude and RustDL, and does not reproduce the
v1.4.5 success on ORE 7345. It predates this IRI repair and the subsequent
partial-saturation and successor-work-budget fixes.
