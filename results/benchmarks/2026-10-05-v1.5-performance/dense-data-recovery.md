# Dense data-ABox routing and singleton-index experiment

The frozen worker traces put ORE 15680 and 4609 on the nominal fallback after
the direct bridge declines their data ABoxes. Each has 205 source classes,
2,111 data assertions, about 4,282 named individuals, and 13,556 logical axioms.
The existing exact ground-source compiler supports them, but the automatic
scheduling hint excluded their size.

Explicit source-compiler job **53313783**, using the original 240-second,
20-GiB, one-CPU limits, verifies ORE 15680 in 61.65 seconds and ORE 4609 in
60.36 seconds. Both agree with independent full-DL references. The same job
times out on the larger-terminology ORE 11378 and 12191; these remain outside
the new dense scheduling bound. This four-case diagnostic is not a release
performance panel.

Automatic scheduling now permits dense functional data ABoxes with at most
512 classes, 20,000 logical axioms, 4,096 positive data assertions, and 8,000
combined source individuals plus data assertions. The 4-MiB source cap,
complete source compilation, import/rule handling, and native coverage checks
remain mandatory. This changes which exact attempt runs, not its semantics.
The standard artifact `ba955555af71` verifies both inputs through automatic
routing with Konclude, HermiT, Openllet, and RustDL agreement.

Five scheduling tests pass. The configured library suite passes 2,709 tests
with eight ignored. All four exact-source Lean gates pass without `sorryAx`.
Source and binary hashes are in `dense-data-source-manifest.json`,
`dense-data-certification-receipt.json`, and `dense-data-standard-check.json`.
Local diagnostic timings are not release speedup measurements; the first
standard check briefly overlapped another local diagnostic on the same CPU.

An optional `KM_HT_SINGLETON_SCAN_AFTER_MERGE=1` experiment replaces repeated
whole-index rebuilding after a singleton merge with the existing direct
per-concept scan. It selects the same first two live positive carriers in
node order and reads their current dependency track points. The reference
index/direct-scan differential tests cover shared labels, local shadowing,
descriptor changes, dependencies, node liveness, and rollback boundaries.
All 1,474 hypertableau tests pass with this option enabled. One local pair on
ORE 15680 gives 44.12 seconds with the option and 47.93 seconds without it,
with byte-identical complete answers. The option remains disabled by default;
repeated paired measurements are still required before promotion.

Frontend validation of the preceding IRI repair remains separate. The strict
audit exposes clause-order changes on ORE 13404 and 6446: nominal defining
clauses are sorted by internal proxy name, so renaming changes their outer
order. `compare_frontend_clause_multiset.py` requires the exact same clause
multiset after source-bound renaming, preserving multiplicity and every
ordered body, head, term, role chain, and other metadata field. Corruption
checks reject dropped/duplicated clauses, changed concepts, and reversed
bodies. Follow-up job **53313782** checks the retained failed outputs.

The original invalid-input check passed 199 of 212 cases. Nine failures came
from the checker's overly narrow diagnostic spelling; four inputs pass the
standalone frontend but fail later classification admission. Revised job
**53314782** requires identical old/new return codes and output bytes for all
212 inputs, accepting the documented line-numbered refusal format. It does
not count any invalid input as a solved ontology.

The old forced-nominal frontend exceeds both the original 20-GiB comparison
cap and a separate 64-GiB validation cap on ORE 15687. This remains unresolved;
matching resource failures do not prove equivalence. No classification limit
or failure denominator has changed. Full classification measurements and the
v1.5.0/v1.5.1 acceptance criteria remain outstanding.

The completed reconciliation accounts for all 1,920 inputs: 1,654 have
byte-identical output, 54 match after source-bound renaming, three additionally
require outer clause reordering, and 208 retain identical invalid-input
refusals. ORE 15687 remains unresolved. Thus preservation is established for
1,919 inputs, and the full frontend gate is explicitly **not passed**.
Candidate classification sweep **53315705** uses the frozen full corpus and
original limits, with the singleton-scan experiment disabled.

Follow-up on 2026-10-06: automatic ordinary `ofn` job **53316202** also exceeds
20 GiB. Production classification instead selects `symbolic_source` before
the ordinary frontend for this source's large cardinalities. We built the
same diagnostic helper against exact engine snapshots `54c91c65` and
`190d5401`, verified all 376 source files in each snapshot against Git, and
compared every symbolic frontend field. Both completed under 20 GiB/240 s.
All 175,535,414 output bytes match, including clauses and all metadata.
See [the receipt](15687-symbolic-preservation.json) and
[source/build provenance](15687-symbolic-source-verification.json).

The helper exhaustively destructures `FrontendResult`, so omitted or added
fields fail compilation. It uses `ofn_to_symbolic_frontend` with the same
trigger-absorption default as `symbolic_source::classify_text`; it does not run
reasoning. The package was cleaned between snapshot builds to prevent Cargo
from reusing artifacts with equal relative paths and older archive timestamps.
The comparison uses diagnostic builds, not the frozen release executables.
It closes the source-level preservation question for this production
representation, but does not establish ordinary-frontend equivalence or
change the failed original gate to a pass. No release target is established.

The earlier full candidate sweep **53309442** has completed all 1,920 inputs.
It verifies **1,613** admitted inputs with mean **7.5992 s** and median
**0.3879 s**, retaining every one of v1.4.5's 1,591 verified solutions and
adding 22. It produces 1,614 complete outputs; one lacks corroboration.
The other admitted outcomes are 34 process errors and 60 timeouts. All 212
invalid inputs remain refused. There are no audit errors.
On the 1,591 shared KM successes, mean runtime falls from 10.8916 to 7.1805 s
and median from 0.6913 to 0.3757 s. This candidate still fails the full v1.5.0
comparison against Konclude and RustDL; the frozen check remains unapproved.
See [the complete summary](data-source-final-summary-53309442.json) and
[release-target comparison](data-source-final-release-check.json).
The newer work-budget and dense-data candidates remain separate sweeps.
