# bridge-self: the saturation SELF rule

Agent `bridge-self`, branch `fix/v155-bridge-self` (base
`development/v1.5.5` at 68ad4132). Design and exactness argument:
docs/HYBRID-CB-HT.md section 20.

## What changed

The bridge's approximation saturation refused every terminology with a
`CCSELF` concept (`applySELFRule` was a `todo!`). On ore_ont_12128 (two
`ReflexiveObjectProperty` axioms, encoded as `⊤ ⊑ ∃R.Self` exactly as
Konclude does) every one of its 187,518 classes then needed its own
completion job.

1. Port of `applySELFRule` (cpp 6843–6890, `saturation/s03.rs`): for each
   entry of the role's indirect super-role list, add the domain and range
   concepts and install a self-connected backward-propagation link
   (`addSelfConnectedBackwardPropagationLink`, aligned with
   `CRoleBackwardSaturationPropagationHash.cpp` 82–93 in
   `process/context.rs`), replaying the pending universal restrictions.
2. The concept saturation no longer refuses SELF
   (`saturation_refuses_self_terminology`); the native-nominal individual
   saturation keeps the refusal (its cache writer has no
   `collectSelfRestrictionRoles`).
3. Three guards that are not in Konclude, each one only deferring work to
   the exact completion: a self edge on a role with disjoint roles, and a
   self edge on a role that an at-most restriction of the node constrains,
   flag the node INSUFFICIENT; and when the terminology has a SELF concept
   that can create a self edge (all but irreflexivity concepts), the bridge
   installs neither expansion cache (`KM-SOUNDNESS-GATE[self-satexp]`).
   The last two are backed by HermiT disagreements of the unguarded port.
4. The incomplete base answer on ore_ont_12128 (coordinator finding): the
   base publishes 1,567 of Konclude's 4,716 unsatisfiable classes at about
   230 s. Cause: the satisfiable expander cache in the completion jobs of
   a SELF terminology (point 3, last gate). Details below and in section 20.

`KM_BRIDGE_SAT_REFUSE_SELF=1` restores the old behaviour completely (the
refusal and no cache gate); every "before" column below is the same binary
with that switch. For an input without a SELF concept the switch is never
consulted on a path that differs, so its before and after runs execute the
same code.

Commits: e0b1cb33 (SELF rule, refusal lifted), 4553fe6b (at-most guard and
first cache gate), 1ecbd86c (irreflexivity concepts excluded), b27044ca
(cache gate on every SELF terminology, the 12128 cause; integration target
`engine/tests/bridge_self.rs`; section 20), cd50e153 and 29d6d6c1 (section
20), ffa646e0 (no saturated-label successor expansion with self edges),
plus the results commit.

## ore_ont_12128

Release flags, ws, alone, `tools/one.sh` (`CAP` sets the cap), reference
check `compare_ref.py` (`data/runs-summary.tsv`):

| configuration | cap | wall | peak RSS | answer |
|---|---|---|---|---|
| before (`KM_BRIDGE_SAT_REFUSE_SELF=1`, = base 68ad4132) | 240 s | timeout | 2.18 GiB | none |
| before | 400 s | 229.8 s | 2.74 GiB | Konclude: taxonomy disagreement (1,567 of 4,716 unsatisfiable) |
| after (ffa646e0) | 240 s | 36.9 s | 2.19 GiB | Konclude: agreement |
| after | 400 s | 37.0 s | 2.19 GiB | Konclude: agreement |

The saturation answers 4,716 unsatisfiable and 182,661 satisfiable subjects
of 187,518 in 4.8 s (141 go to completion). The frontend takes about 12 s
and the bridge part ends 16 s after the CB stack starts; the remainder of
the wall time is outside the bridge. Konclude needs 22 s.

**The incomplete base answer.** The 3,149 classes the base misses are all
reported satisfiable (`data/12128-incomplete/12128-missed-unsat.txt.gz`); no
class is wrongly unsatisfiable. A reachability module of one of them
(`m53.ofn`, 1,165 axioms; `tools/reach_module.py`) reproduces it (28 of
HermiT's 40 unsatisfiable classes on the base, 40 with
`KM_HT_NO_SAT_EXP_CACHE=1`, 40 on the branch), and `tools/ddmin.py` reduces
it to 23 axioms (`m53tiny.ofn`, HermiT gold beside it): an unsatisfiable
class without any self edge is published satisfiable as soon as a reflexive
role and an unrelated functional role are present, and only while the
satisfiable expander cache is installed. The fix is the gate
`KM-SOUNDNESS-GATE[self-satexp]` (no expansion caches and no saturated-label
successor expansion on a terminology with a SELF concept that can create a
self edge). I did not isolate the cache entry that goes wrong; the gate
removes the cache on every such terminology, so it covers the whole class
of cases, at a measured cost of nothing on 12128 (36.9 s with the gate,
38.8 s without it in an earlier build) and up to 10 percent on the
SELF-bearing nominal inputs below.

## Held-out inputs (docs/V1.5.5-STATUS.md, "Konclude coverage gap")

Release flags, 240 s, two at a time, 12128 alone (`tools/heldout.sh`).
Only 6132, 9899 (irreflexive roles) and 12128 (reflexive roles) have SELF
concepts; for the other 13 the branch runs the base's code (no SELF concept,
so neither the rule, the guards nor the gate is reached), and their rows are
the noise reference.

| input | before | after | answer after |
|---|---|---|---|
| 4903 | (4.4) | 4.0 s | Konclude: agreement |
| 11647 | (5.3) | 4.9 s | agreement (Konclude, HermiT, Openllet) |
| 4796 | (3.3) | 3.5 s | agreement |
| 3917 | (5.5) | 5.5 s | Konclude: agreement |
| 11378 | (7.9) | 6.9 s | Konclude: agreement |
| 12191 | (8.5) | 7.9 s | Konclude: agreement |
| 9151 | (81.8) | 71.0 s | Konclude: agreement |
| 9577 | (101.3) | 104.6 s | Konclude: agreement |
| 6132 | 10.1 s | 9.3 s | Konclude, HermiT: agreement |
| 9899 | 11.5 s | 10.2 s | Konclude, HermiT: agreement |
| 16315 | (38.5) | 36.7 s | Konclude: agreement |
| 10838 | (74.0) | 70.4 s | Konclude: agreement |
| 3087 | (93.2) | 67.5 s | Konclude: agreement |
| 7557 | (149.5) | 104.5 s | Konclude: agreement |
| 10926 | (rc=1, 213 s) | rc=1, 235 s, 18.0 GiB | no answer (unchanged) |
| 12128 | timeout | 36.9 s | Konclude: agreement |

Values in parentheses are `.work/v155-heldout-gap/combined/summary.tsv`
(build 63d6e63e, an older base); the before values of 6132 and 9899 are
this binary with `KM_BRIDGE_SAT_REFUSE_SELF=1`. Every answer is kept.

An intermediate build that gated the caches on every SELF concept,
including irreflexivity, sent 9899 from 11.5 s to a timeout; 1ecbd86c
excludes irreflexivity concepts (they never create a self edge).

## 112 nominal ORE design-half inputs

`tools/ore_nominal.sh` (the `ore_time.sh` of r3-unannounced, 300 s, one
process, release flags), before and after, paired with `tools/ore_pair.py`
(`data/ore-nominal/`): 109 answered by both, 109 identical signatures, no
answer-status or route change; ratio after/before over the 27 inputs above
1 s: mean 0.985, median 0.985, max 1.66 (16666, 3.2 to 5.3 s; a rerun of
the three highest ratios gives 4.2/4.4, 1.7/1.6 and 15.6/16.3 s,
`rerun-slow.txt`, i.e. noise; none of them has a SELF concept). The four
inputs with SELF constructs (12451, 2548, 7532, 9662) on the final binary:
see "Final pairing of the SELF nominal inputs" below.

## SELF seed family (new)

`tools/gen_self.py`, 2,000 seeds `s0..s1999`, HermiT gold through
`tools/gold.sh`, seeds and gold in `.work/agent-scratch/bridge-self/pool/`.
Even seeds are Horn (no unions, no negated atoms or self restrictions, no
at-most inside class expressions, rare irreflexive/asymmetric/disjoint
roles), odd seeds the full mix. Constructs: self restrictions at the top,
under existentials, universals, min and max cardinalities, conjunctions and
disjunctions, negated; inverse roles in existentials, universals and
cardinalities; sub-, equivalent and inverse properties; a transitive role
with simple sub-roles; domains, ranges; functional, inverse-functional,
reflexive, irreflexive, asymmetric and disjoint properties; nominals
(ObjectOneOf, ObjectHasValue) in a quarter; small ABoxes in a quarter. The
frontend takes only named roles in `ObjectHasSelf` and
`SubObjectPropertyOf`, so the generator uses those forms.

Both routes, 60 s cap, release flags, two runs at a time (`tools/seeds.sh`,
`tools/diff_run.py`, `tools/seed_compare.py`; `data/seeds/`):

| column | ok | ERR | TIMEOUT | WRONG |
|---|---|---|---|---|
| before | 3,738 | 249 | 11 | 2 |
| after (final) | 3,739 | 248 | 12 | 1 |

Transitions: `s1966` auto WRONG to ok (flaky, see below) and `s284`
`ht_bridge` ERR (no answer after 34 s) to TIMEOUT (no answer). No new
difference with HermiT. The one WRONG row in both columns is `s974` on the
automatic route, which the CB engine answers alone (`in-process engine (no
race)`): it misses `Q2 ≡ E ⊓ ≥2 r.Self(p)` as unsatisfiable under
`Reflexive(r)` and `InverseFunctional(r)`; the bridge route is right. That
is a CB calculus defect outside this branch's scope. `s1966` misses
`C ⊑ Q3` (`Q3 ≡ ∃r.Self`, `r` reflexive) intermittently on the automatic
route in both configurations (CB stack; `data/s1966-flaky.txt`: 11 of 12
runs wrong after, 10 of 12 before).

ERR rows are the bridge declining on the forced route (`ontology is
outside the native HT bridge certificate`, e.g. disjoint object
properties); the automatic route answers them.

Saturation coverage on the family (`data/seeds/self-saturation-coverage.txt`,
forced route): 1,164 seeds run a saturation pass, 72 of them get
saturation verdicts (62 unsatisfiable and 46 satisfiable subjects of
12,791); the small seeds mostly send their classes to completion (insufficient
nodes, classes without a saturation node). The family therefore exercises
the completion's saturation coupling more than the verdicts, which 12128
exercises at scale.

The unguarded port (first build) was WRONG on six seeds of an earlier
generator version; they are kept as `data/regress/v1s*.ofn` with HermiT
gold and pass on the final build, and five of them are fixtures of
`engine/tests/bridge_self.rs`.

