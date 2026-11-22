# Errata for KM v1.5.1 to v1.6.5

Published with KM 1.7.0 (unreleased). It covers every release from v1.5.1
to v1.6.5.

## Summary

These releases can give a wrong answer on inputs that combine functional or
inverse-functional properties (object or data) with merges of individuals or
successors. The answer can miss:

- an inconsistency (KM says "consistent", the ontology is inconsistent);
- unsatisfiable classes (KM says "satisfiable");
- subsumptions that follow from the missed unsatisfiable classes or from
  lost blocking decisions.

In the cases we know, the wrong answer is a missed consequence. Because the
answer is too weak, a missed inconsistency also means that every
subsumption and every unsatisfiable class that the inconsistency entails is
missing. We have not found a case where KM reported a consequence that does
not hold. This comes from the fuzz cases and commit messages named below.
We did not prove that no such case exists.

On the 1,708-input ORE pool, no input changed its answer with the fix. The
paired runs on Ibex (a v1.7.0 build with the fix against the build before
it) agree on all 1,696 inputs that both solved. Inputs outside the pool can
still be affected. The defect needs a
particular combination of axioms (see the reproducers).

KM 1.7.0 fixes the defects. If you use an earlier release and your ontology
has functional or inverse-functional properties together with merges, check
the answer with a second reasoner or upgrade.

## Reproducers

Both are in the KM tree (scratch, not shipped) and are small enough to
read.

1. `v101_13.base.min.ofn` (41 lines): a missed inconsistency. An
   individual becomes its own successor through merges and carries two
   values of a functional data property (`d0(a5, 1)` and `d0(a5, 2)`).
   KM answers `CONSISTENT 1`. HermiT answers inconsistent. Path:
   `/mnt/data1/leechuck/km-work/v170/scratch/engine10/w4/repro/v101_13.base.min.ofn`.
2. `case3_c3min.ofn` (14 lines): a missed unsatisfiable class.
   Path:
   `/mnt/data1/leechuck/km-work/v170/scratch/missed/konclude-check/in/case3_c3min.ofn`.
   Axioms, in prose: `s ⊑ r`, `r` is functional, `A ⊑ ∃s.B ⊓ ∃s.C`,
   `B` and `C` are disjoint, and `A ⊑ ∃inverse(ri).B ⊓ ∃r.A`. Then `A` is
   unsatisfiable (the two `s`-successors of `A` merge, because `r` is
   functional, and clash). KM reports `A` satisfiable. HermiT reports `A`
   unsatisfiable.

The other cases found in the same work are fuzz inputs named `v101_13`,
`v404_79` (inconsistency), `v303_10` and `v303_300` (unsatisfiable
classes), and the blocking and template-nominal cases in the notes under
`/mnt/data1/leechuck/km-work/v170/scratch/missed/`.

## Causes and fixes

Three defects, all in the hypertableau bridge, were found in this campaign.
The first two inherit the design of Konclude's saturation and completion
code. Fix commits are in KM 1.7.0.

1. **A declined saturation cache confirmed a label** (`19b80195`, then
   `af790502`). The cache attempt on a completion node recorded a "last
   confirmed" marker even when it found a concept that the saturation node
   lacked, or when it declined because of a nominal connection. The retest
   read the marker as "the label is still covered" and treated the node as
   cached. On inputs where merges make an individual its own successor,
   that individual was never expanded and its clash with a merged value
   never arose. The defect comes from the saturation coupling port
   (`1b57b9d6`, 2026-07-10). A later change (`980877fe`, then `55117da2`)
   hid it for one day.  The first fix was narrowed to reused nominals
   (`bc6fb99f`, a development commit) and `af790502` extends it to reused
   successors whose label the new saturation node does not cover. After the fixes, 4,920 standard and 2,400
   blocking random cases agree with HermiT.
2. **One polarity per concept in the functional merge** (`8a34a1e3`). The
   saturation merges all successors of a functional role by extending a
   copy of a base node. Its extension map was keyed by concept and kept one
   polarity, so two successors with `B, ¬C` and `¬B, C` lost their clash.
   The map now records the conflict, and the merging node is marked
   insufficient, so the completion graph decides it.
3. **Blocking read only the reapply queue** (`c11e5db6`). The optimized
   blocking test read the blocker's universal and at-most restrictions from
   its reapply queue only. A restriction that was never applied counted as
   absent, so a blocker could block a successor wrongly and subsumptions
   were lost. This was found on the v1.7.0 line (a blocking-focused fuzz:
   22 wrong rows in 1,200 cases on build `ebe741b4`, none after the fix).
   We did not test which earlier releases show it; we list it here because
   the code path is the same one.

## Which releases

The commit messages record binaries of v1.5.1 to v1.6.2, v1.6.4-rc1 and a
v1.6.5 build as wrong on the inputs of defect 1, and v1.5.1 to v1.6.2 and
v1.6.5 for defect 2. The releases between these (v1.5.2 to v1.5.5,
v1.6.0, v1.6.1, v1.6.3, v1.6.5 itself) share the code. We list them
as affected without running each tag on the reproducers. Releases before
v1.5.1 predate the saturation coupling and we did not test them.

## Upstream Konclude shows the functional-merge defect too

We ran unmodified Konclude v0.7.0-1138 on the reproducers and on the fuzz
cases, next to HermiT. Table:
`/mnt/data1/leechuck/km-work/v170/scratch/missed/konclude-check/table.txt`.

- On `case3_c3min.ofn` (and its sibling `case3_t38`), Konclude does not
  report `A` unsatisfiable, where HermiT does. The supervisor confirmed
  this case. That is the functional-merge defect (defect 2) in Konclude
  itself.
- On the two inconsistency cases (`case1_v101_13`, `case2_v404_79`) and on
  the template-nominal case, Konclude agrees with HermiT.
- The table lists other differences between Konclude and HermiT on fuzz
  cases from the development line. We did not decide these in this
  document, and we do not claim them as Konclude errors.

## What to do

- Upgrade to KM 1.7.0 when it is out.
- Until then, for an ontology with functional or inverse-functional
  properties and merges (for example through nominals or number
  restrictions on functional roles), check "consistent" and "satisfiable"
  answers with a second reasoner.

## Related notes

The v1.6.5 release notes (`docs/RELEASE-1.6.5.md` at the tag `v1.6.5`)
state that 10,000 random knowledge bases showed no wrong KM answer against
HermiT. That statement is true of those sets. The defects above need
inputs that those sets did not contain, so it does not rule them out.
