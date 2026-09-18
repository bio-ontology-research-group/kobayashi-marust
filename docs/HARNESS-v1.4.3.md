# Michel harness bugfix validation

This records the fixes and validation for v1.4.3. The [complete evidence report](../results/benchmarks/2026-09-18-v1.4.3-harness/README.md)
contains all process outcomes, recovered-answer checks and remaining failures.

## Reproduction

The harness is `micheldumontier/owl-reasoner-harness` at
`7559c4543b270eb3a26cc88a6d4e837cffa0b84f`. The corpus is all 1,920 ontologies
in Zenodo record 18578's `ore2015_sample.zip`, MD5
`109f04cf8f124eb551d33c100e549730`. Each input also has a retained SHA-256.

Runs use Slurm on IBEX, one allocated CPU, `RAYON_NUM_THREADS=1`, a 240-second
external deadline and a 20-GiB address-space limit. Slurm allocates 22 GiB.
The v1.4.2 baseline uses its published binary through the harness's v1.4.0
wrapper with `KM140_BIN` explicitly identifying v1.4.2. The wrapper selects
`auto`. rustdl is the harness-pinned v0.4.28 Linux musl binary.

The completed v1.4.2 baseline has 1,816 `ok`, 61 `err_reject`, 33 `dnf` and
10 `declined` outcomes. These are process outcomes, not correctness verdicts.
The rustdl panel completed with 1,806 `ok`, 106 `dnf` and eight errors.
The final KM panel completes 1,829 inputs,
recovering 13 baseline failures with no lost baseline completion
and no changed jointly completed output hash. Candidate arrays
started with eight concurrent tasks and increased to sixteen after the
scheduler left capacity idle. The final candidate increased from sixteen to
thirty-two after 906 matching CPUs were reported idle. The per-ontology allocation and limits did not
change; `scheduling-amendment.json` records the transition. These runs test
coverage and answer preservation, not repeated performance or speed ranking.

## Worker outcomes

The supervisor already knows whether its deadline or RSS watchdog killed a
worker. Previously the orchestration error discarded those flags and reduced
any signal termination to `-1`. Internal 190-second deadlines consequently
appeared as generic engine errors in the harness.

The patch preserves observed timeout and memory-limit outcomes. A deadline
returns CLI status 124. An independently received Unix signal retains its
signal number and is not classified as a timeout. RSS-limit failures retain
their diagnostic rather than guessing from a signal number.

## Query scheduling and proof allocation

Rayon already honors the harness's thread budget. KM's route settings still
requested sixteen independent saturation tasks, which repeated the nominal
ground closure on a single active worker. Small static nominal query sets now use the
available CPU/Rayon budget. Non-nominal inputs and large nominal query sets
retain their original partition count, which bounds the conditional labels accumulated in each
ground context. Reducing all query sets to a single partition regressed a
large ontology by reaching the per-engine message backstop; that experiment
is not the final scheduling policy. A subsequent sweep observed a timeout on `ore_ont_3215`, whose baseline
completed in 169 seconds. The final policy limits the optimization to its
intended small static nominal inputs and preserves the established schedule
elsewhere. The narrowed candidate also timed out in an initial replay, so
the scheduling change alone cannot explain that observation. A repeated
comparison in one Slurm allocation is retained separately from the primary
panel to distinguish timing variability from reproducible regression. In that
ABBA replay, v1.4.2 timed out once and completed once in 221.47 seconds;
the candidate completed twice in 216.04 and 216.45 seconds. Every completed
answer has the same output hash. Timing traces show the existing sequential
bridge handled the case, rather than the modified CB task path. These
observations do not establish a speed ranking. The final primary sweep also
completes 3215 in 162.56 seconds with the same output hash; this original
primary observation is retained rather than replaced by a replay.

Hyper previously allocated owned provenance vectors for every prospective
resolvent even when certificate history was disabled. The patch constructs
those vectors only when recording that history. The resolvent builder,
inference order and certificate-enabled evidence remain unchanged.

These changes alter scheduling and allocation, not the CB inference rules.
Terminal-state and certificate regression tests guard that distinction.

## Functional string ABox projection

A functional data property with assertions `p(a, "left")` and
`p(b, "right")` entails `a != b` when the string values differ. Removing the
assertions without retaining this inequality would be unsound: later object
reasoning could merge the two owners.

The new bounded projection retains every such owner inequality in the typed
ABox and, in nominal mode, the CB clauses. It admits only plain or explicitly
`xsd:string` values, validates all ranges, and requires every domain type to
follow from an existing class assertion through named subclass links. It declines property hierarchies, keys,
negative data assertions, conditional data cardinalities, other interacting
data restrictions, and escaped functional values. At most 256 source data
assertions are considered. Unsupported cases keep their previous route.

The projection preserves object consequences in both directions. Every source
model satisfies the retained owner inequalities. Conversely, extend any model
of the reduced object ontology with the asserted string edges. The inequalities
ensure that an equality class never receives two different values for one
functional property. The entailed domain memberships and checked ranges satisfy
the remaining data obligations; the admission checks exclude further
interactions. Consequently consistency and named object-class subsumption are preserved.
The bridge independently checks the resulting native input and may still defer.

The motivating ontology is `ore_ont_11895`: thirteen functional string facts
produce 78 owner inequalities. In the final candidate's matched one-CPU run,
the original, unmodified input completes in 0.038 seconds, versus the released
baseline's internal deadline. Its 256 subsumption pairs, consistency verdict
and unsatisfiable set agree exactly with both HermiT and JFact. This is a
single coverage observation, not a repeated timing estimate.

## Rejected shortcut

A forced `ht_general` experiment finished several nominal failures quickly.
Some small examples matched both references, but broader checks found lost
relations and a consistency disagreement. The forced path can clear nominal
information and bypass conversion fences. The proposed broad automatic route
expansion was removed. Those experimental completions are not recoveries.

## Comparison rules

Keep completion, source coverage and semantic agreement separate. Of rustdl's 1,806 completed outputs, 99 report incomplete reasoning and 431
report dropped source axioms; 480 have either flag. Of the 78 inputs rustdl
completes that v1.4.2 does not, 65 carry either flag. These flags are not proof
of an incorrect answer, and KM's worker clause count named `dropped` is not
comparable to rustdl's dropped-source-axiom count. A process-level `ok` alone does not establish
that the complete source ontology was classified.

Compare full-IRI taxonomy relations, consistency and unsatisfiable classes.
For inconsistent inputs compare the verdict first: reasoners differ in whether
they emit empty taxonomy sets or mark every class unsatisfiable. Preserve
unsupported cases, timeouts and unverified results in the final ledger.

## Recovered-answer checks

`ore_ont_10391` agrees exactly with both HermiT and JFact. `ore_ont_10754`
agrees with HermiT and with the transitive closure of Konclude's classification
(all 507 named-class relations); JFact instead reports inconsistency. Keep that
reference disagreement visible rather than reporting unanimous agreement.

## Remaining baseline failure categories

Of the 104 baseline non-completions, 58 have the old `-1` diagnostic near the
internal deadline, 33 reach the external deadline, two explicitly report
allocation failure, ten decline unsupported syntax, and one has a signal
termination that the old diagnostic cannot identify. Reporting a timeout
correctly does not count as recovering an ontology.

The ten explicit declines comprise seven unsupported DL-safe-rule inputs and
three inverse-role-chain inputs (`2738`, `2874`, `8250`). The latter require
inverse expressions in both normalized chain clauses and typed RBox metadata;
accepting them in the parser alone would leave an incomplete bridge input.
They remain explicit limitations in this release candidate.
