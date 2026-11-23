# Errata for KM releases up to v1.6.5

Published with KM 1.7.0 (unreleased). It covers every release from v1.5.1
to v1.6.5, and says for each item whether v1.6.5 has it. The reproducers
are small `.ofn` files in `docs/errata/1.6.5/`.

## Summary

KM gave wrong answers on some inputs. In most cases we know, the answer was
too weak: KM missed an inconsistency, an unsatisfiable class or a
subsumption. A missed inconsistency also means that the subsumptions and
unsatisfiable classes it entails are missing. Two items go the other way:
the rule-worker self atom reports "inconsistent" for a consistent ontology,
and `DisjointClasses(B D D)` reports `D` unsatisfiable. Both need the input
described in the table.

We have not proved that no other wrong answer exists. The list comes from a
64,000-case differential campaign against HermiT, two TBox sweeps of 20,200
cases on 13 routes, fuzz runs and the pool gates.

**No input of the 1,708-input ORE pool changed its answer with the fixes.**
Every fix passed a paired pool run on Ibex (the build with the fix against
the build without it) with 0 answer differences on the 1,696 inputs that
both builds solved. The other 12 inputs are not solved by both builds.
Inputs outside the pool can still be affected.

Upgrade to KM 1.7.0 when it is out. Until then, check "consistent" and
"satisfiable" answers on ontologies that match the shapes below with a
second reasoner.

## How to read the table

- "Route" says where we saw the wrong answer. The automatic route (`auto`)
  is what `km classify` and the Protégé plugin run. Several defects sit in a
  single arm of the automatic route, and another arm can answer correctly on
  a small reproducer. Forced routes (`--route R`) show the defect directly.
- "v1.6.5" says what we saw with a build of the v1.6.5 head (`55117da2`) on
  the file named, using `km classify --lines`, one thread. "Not run" means
  we rely on the commit message only.
- Files are in `docs/errata/1.6.5/`.

| Item | v1.6.5 | What a user sees | Reproducer and route |
|---|---|---|---|
| Saturation cache confirmed a label (`19b80195`, `af790502`, `554a72e7`) | has it (seen) | "consistent" for an inconsistent ontology; the unsatisfiable classes are listed as satisfiable. Needs merges that make an individual its own successor and a functional data property with two values. | `saturation-cache-v101_13.ofn`, `saturation-cache-v404_79.ofn`; auto prints `CONSISTENT 1` where HermiT says inconsistent |
| Functional merge, one polarity per concept (`8a34a1e3`) | has it (seen on a forced route) | A class that needs two disjoint fillers of a functional super-role is satisfiable. | `functional-merge-case3.ofn`; forced `ht_bridge` gives no `UNSAT :A`. On auto the same file is right, because another arm answers. |
| Value merges in saturation (`6b5e1613`) | has it (seen) | `A ⊑ ≥2 d` with a range of one value gives `A` satisfiable. | `value-merge-singleton.ofn`; auto, no `UNSAT :A` |
| Universals over transitive roles (`a111e343`, `eb04beb3`, `d21a49e0`) | has it (seen on forced routes), since the first Rust frontend (`d155df34`) | A subsumption that needs a `∀` over a transitive role along more than one edge is missing on the CB routes, and on auto when the HT bridge declines. | `transitive-universal.ofn`; forced `cb_plain1` and `lean` lack `SUB :Q :F` |
| N-ary axioms with repeated operands (`f2710130`, `bfb7be93`) | has it (seen) | `DisjointClasses(B D D)` makes `D` unsatisfiable on every route. The same holds for `DisjointUnion`, `DifferentIndividuals`, `DisjointObjectProperties` and `DisjointDataProperties`. | `nary-disjoint-repeated-operand.ofn`; auto gives `UNSAT :D` |
| Cardinality fillers missing from HT rows (`04a49e49`) | has it (commit message) | A named class that occurs only as a qualified cardinality filler has no rows on the HT cardinality arms. | No small file reproduces it; sweep case `card20044_0044`; not run |
| Bridge root label from the substitute chain (`ee79d91a`) | has it (seen) | Subsumptions such as `B ⊑ Q0` are missing, with `DROPPED 0`. | `bridge-root-substitute-chain.ofn`; auto lacks `SUB :B :Q0` |
| HT cardinality number rule (`4acc762d`, `c6ff52f6`) | has it (seen on a forced route) | A class is reported unsatisfiable, or an ontology inconsistent, because a `≤n` marker was derived without a decision. | `ht-card-number-rule.ofn`; forced `ht_card` gives `UNSAT :F` |
| Certified EL arm, dead-node rule (`1f71bc91`) | has it (seen) | `SUB X Q0` rows are missing, with `DROPPED 0`. | `el-arm-dead-node.ofn`; auto lacks the `Q0` rows |
| Separability with a nominal in a domain or range (`482a3458`) | has it (seen) | The automatic route classified the TBox alone, and a subsumption that needs the ABox is missing. | `nominal-domain-range-separability.ofn`; auto lacks `SUB :Pr :Ps` |
| Nominal CB routes miss labels of individuals (`30c850c4`, `a84969a4`, `9bd68cb6`, `24d50930`) | has it (seen on forced routes); every release | "consistent" for an inconsistent ontology, and missing subsumptions. In the cases we have, only the forced `nominals` and `certified_nominals` routes are wrong; the automatic route answers through the bridge. | `nominal-cb-individual-labels.ofn`; forced `certified_nominals` prints `CONSISTENT 1` |
| Rule worker, self atom (`b15cf0d8`) | has it (seen on a forced route), since v0.1 | An irreflexive role with a key or a DL-safe rule and one `r` edge gives "inconsistent" for a consistent ontology on the forced rules routes. | `rule-worker-self-atom.ofn`; forced `ht_rules` prints `CONSISTENT 0` |
| Plugin: values through anonymous individuals (`b6cb3438`, `34f9e651`) | has it (parity run) | `getObjectPropertyValues(a4, c1)` returns `{}` and `isEntailed(c1(a4, a4))` is false, where HermiT says `{a4}` and true. | `plugin-values-through-anonymous.ofn`; plugin only, not run here |
| OWL/XML input (GitHub issues #6 and #7) | has it (issue reports) | #6: conversion wrote relative IRIs such as `/A`, which the front end rejects. #7: `km features` showed zero constructs for OWL/XML, RDF/XML and Turtle input. | Needs an OWL/XML file; see the tests added with `df2529cf` and `42da1e86` |
| Source spelling of rows (`ad777d85`) | has it (commit message) | With a functional data property that has a facet range and data assertions, rows came out as full IRIs where the source and HermiT use `:A`. | Not run |

Issues #6 and #7 were reported by Michel Dumontier.

Not in v1.6.5, so no erratum: the `--different` model plan (several causes
found in the campaign), the `--data-properties` probe with different ranges,
and the frontend `DataHasValue` pass on forced nominal routes. They were
found and fixed in the v1.7.0 development.

Found in the same campaign and not tested against v1.6.5: the optimized
blocking test read only the reapply queue of the blocker (`c11e5db6`). A
blocking-focused fuzz found 22 wrong rows in 1,200 cases on a v1.7.0
development build before the fix, and none after it.

## Notes on three items

**Saturation cache.** The cache attempt on a completion node recorded a
"last confirmed" marker even when it found a concept that the saturation
node lacked, or when it declined because of a nominal connection. The retest
read the marker as "the label is still covered". The defect comes from the
saturation coupling port (`1b57b9d6`, 2026-07-10). A stopgap (`980877fe`)
hid it in the v1.6.5 line; the last commit before the tag (`55117da2`)
switched the stopgap off. With the build one commit earlier (`60383939`)
the two inputs `v101_13` and `v404_79` give the right answer; with the
v1.6.5 head they give "consistent". After the fixes, 4,920 standard and
2,400 blocking random cases agree with HermiT.

**Functional merge.** The saturation merges all successors of a functional
role into one node by extending a copy of a base node. The extension map was
keyed by concept and kept one polarity, so two successors with `B, ¬C` and
`¬B, C` lost their clash. The commit message says the wrong answer appears
in `--realize` rows of v1.6.5 on a fuzz case (`v303_10`). On the small files
we could reproduce it only with the forced `ht_bridge` route.

**Value merges.** The bridge merges two data successors that carry the same
literal. The saturation did not, so `A ⊑ ≥2 d` over a property with one
allowed value stayed satisfiable. The defect dates from the singleton merge
(`d58c2b2e`). The commit message names v1.5.5, v1.6.0 and v1.6.5 as wrong.

## Which releases

The commit messages name binaries of v1.5.1 to v1.6.2, v1.6.4-rc1 and v1.6.5
as wrong for the saturation cache and the functional merge, and v1.5.5,
v1.6.0 and v1.6.5 for the value merge. For the nominal CB routes the
message says every release. For the other items it says "v1.6.5 has it". We
list the releases in between as affected because they share the code. We did
not run each tag. Releases before v1.5.1 predate the saturation coupling; we
did not test them.

## Upstream Konclude

We ran unmodified Konclude v0.7.0-1138 next to HermiT on the reproducers.
The first set is in
`/mnt/data1/leechuck/km-work/v170/scratch/missed/konclude-check/table.txt`.
The second set is the output of `kc2.sbatch` under
`/ibex/scratch/hohndor/missed-170/kchk2`.

- Functional merge: on `functional-merge-case3.ofn` (and its sibling
  `case3_t38`) Konclude does not report `A` unsatisfiable, where HermiT
  does. The supervisor confirmed this case.
- Value merge: on `value-merge-singleton.ofn` Konclude's classification
  lists `A` only below `owl:Thing`, so it reports `A` satisfiable. The
  correct answer is unsatisfiable: the range allows one value and the class
  needs two. This is one input and one run. We have not looked into the
  cause. The commit message for the KM fix says that Konclude reads literals
  in its data box and has no value singleton concept, so the cause in
  Konclude may differ from the one in KM.
- On the two inconsistency inputs of the saturation-cache item, Konclude
  agrees with HermiT.
- The first table lists other differences between Konclude and HermiT on
  fuzz cases from the development line. We did not decide them and do not
  claim them as Konclude errors.

## What to do

- Upgrade to KM 1.7.0 when it is out.
- Until then, for ontologies with functional or inverse-functional
  properties, merges, transitive roles with universal restrictions, nominals
  with inverse roles, or repeated operands in disjointness axioms, check
  "consistent" and "satisfiable" answers with a second reasoner.

## Related notes

The v1.6.5 release notes (`docs/RELEASE-1.6.5.md` at the tag `v1.6.5`) say
that 10,000 random knowledge bases showed no wrong KM answer against
HermiT. That is true of those sets. The defects above need inputs that those
sets did not contain, so it does not rule them out.
