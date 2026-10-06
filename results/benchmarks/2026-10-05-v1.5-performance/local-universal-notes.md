# Redundant local datatype universals

The atomic datatype admission collector rejected class-local `Forall` data
restrictions even when the source already declared the identical global range.
The downstream role-use guard and source encoder already support atomic
universals. ORE13799 has this exact shape for float-valued hasMass and int-valued
hasYearOfLaunch. Current-candidate profile job 53326865 confirms the refusal
followed by a nominal fallback and an internal worker timeout.

Admission now collects explicit `Top <= Forall(role, atomic_range)` source
axioms before inspecting local occurrences. It admits a local universal only
when both role and atomic datatype name match an explicit global range.
Source order is irrelevant. The complete original expression stays in the
native encoder; nothing is erased, weakened or treated as an existential.
All existing atomic-vocabulary, clause-evidence, role-use, domain, cardinality
and publication guards still apply. General local universals without the
identical explicit global range still decline.

Two new FunctionalDatatypeQuotient lemmas prove the global-to-local implication
and preservation of a theory when its entailed class-local range is added.
Both are axiom-free and the HT gate audits them. They establish the new
redundancy argument; existing source/typed publication checks remain required.
No saturation or CB calculus rule changes.

All 72 datatype-filtered Rust tests pass, including a new regression that
checks local-before-global source order, exact classification preservation,
unchanged source expressions, disabled source mode, a mismatched datatype and
removal of the global range. All four production certification gates are running against the pinned source
manifest; their receipt is written as each gate finishes. No full-gate pass is
claimed by this note.

A bounded workstation check of unchanged ORE13799 completes in 0.134 seconds
on one CPU under a 30-second diagnostic cap and 20-GiB memory cap. Its known
consistency and complete taxonomy agree with Konclude, HermiT, Openllet and
JFact using the pinned source signature and reference audits. This timing is
not comparable to cluster benchmark timings and does not change the full-run
solved count. The local wrapper first failed because /usr/bin/time is absent;
two subsequent attempts produced answers but failed while serializing watchdog
metadata. The final recorded attempt uses the watchdog's scalar fields.

Slurm job 53327291 tests the same eight coverage failures with the new pinned
binary, the original 240-second/20-GiB/one-CPU contract, and independent answer
auditing. Its artifact explicitly records certification pending at submission;
final gate results live in the source-pinned certification receipt. This is a
diagnostic panel, not a replacement for the complete frozen release corpus.
Both release objectives remain unmet.

The first cluster recovery receipt verifies ORE13799 in 0.181 seconds and
agrees with all four independent references. Four other completed diagnostic
cases remain failures, and three are still running in the partial receipt.
The original failures remain unchanged in the full-corpus benchmark.
