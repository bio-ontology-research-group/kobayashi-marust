# ORE 2015 route validation: tail and source-IRI collision audit

This document records fresh, isolated IBEX validation of the original eight
ontologies outside the 584-row `exact_gold` set in
`ontology-solve-routes.tsv`. It also records the follow-up source audit that
found one hidden false exact match, ontology 13503, and the source-symbol fix
that closes 3524, 13503 and 15703 without regressing 7581. A process that exits
successfully has not solved an ontology unless its result is also sound and
complete.

All runs used a 240-second wall limit, a 20 GiB process-group memory limit and
16 CPUs unless a targeted one-class HermiT query is stated. Raw outputs remain
under:

```text
ibex:/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718
ibex:/ibex/scratch/hohndor/km/routing_20260715/special-iri-fix-20260718
```

Small metadata, hashes and adjudication records are committed under
[`evidence/direct-validation/`](evidence/direct-validation/).

> **2026-07-21 update:** the source-bound capsule-10 replay closes 10621 through
> `KM_ROUTE=ht_bridge` in 118.2149 seconds at 1096.54 MiB. The trace selects
> exactly `ht_bridge`, and KM's full-IRI taxonomy equals fresh source-built
> Konclude at 70,827 subsumptions and 33,433 unsatisfiable named classes. The
> earlier 10621 analysis below remains as historical diagnosis.

> **2026-07-22 reproducibility update:** source-bound IBEX replays reproduce all
> 589 documented correct classifications. The authoritative per-ontology route,
> command, source/build/runtime identities, limits and fresh oracle evidence are
> in
> [`../2026-07-21-route-confirmation/reproduced-route-ledger.tsv`](../2026-07-21-route-confirmation/reproduced-route-ledger.tsv).
> The ledger retains 4669, 10860 and 1194 as explicit nonclaims.

## Validated status

| Ontology | KM terminates in limit | Direct validation | Final state | Route or blocker |
|---|---:|---|---|---|
| 2669 | yes, 0.1177 s | KM and HermiT core both return the same inconsistent signature | solved correctly | `ht_rules`, `KM_HT_RULES=1` |
| 15516 | yes, 0.1187 s | KM and HermiT core both return the same inconsistent signature | solved correctly | `ht_rules`, `KM_HT_RULES=1` |
| 3524 | yes, 35.8973 s | all 123,310 strict told subsumptions are preserved; full-IRI taxonomy equals Konclude and ELK | solved correctly | fixed `production_all` |
| 15703 | yes, 24.4077 s | all 123,310 told subsumptions are preserved; full-IRI taxonomy equals Konclude and ELK | solved correctly | fixed `production_all` |
| 4669 | yes, 15.3261 s | HermiT refutes sampled production UNSAT results and all 56 additional HT UNSAT results | completed but unsound | both retained KM answers are invalid |
| 7581 | yes, 19.2328 s | fixed KM and Konclude full-IRI taxonomies match exactly | solved correctly | fixed `production_all` |
| 10621 | yes, 118.2149 s | fresh source-built Konclude full-IRI taxonomy is exactly equal | solved correctly | `ht_bridge`, `KM_ROUTE=ht_bridge` |
| 10860 | no | production rejects unsupported rules; CB bypass reaches its internal cap | no complete route | SWRL built-ins plus live disjunction |
| 1194 | no | production and HT exceed 20 GiB; HermiT times out and Konclude exceeds 20 GiB | no complete route | large SRIQ ABox saturation |
| 13503 | yes, 0.0627 s | KM emits the legal `daml+oil#Nothing` source class as UNSAT; full-IRI taxonomy equals Konclude and HermiT agrees | solved correctly | fixed `production_all` |

The validated accounting for all 592 inputs is therefore:

- 587 gold-exact KM results;
- 2 independently adjudicated correct results whose stored Konclude files are
  parse-failure artifacts;
- 1 KM run that terminates but returns an incorrect classification;
- 2 ontologies with no complete KM run within the benchmark limits.

The validated correct coverage represented by this registry is **589 of 592**.
Ontology 4669 must not be counted merely because a KM process returned output.

## Validation method

Each reasoner ran in an isolated Slurm allocation. The watchdog retained the
raw output, stderr, wall time, peak process-group RSS, executable hash, ontology
hash, command, environment, host and Slurm task ID. Canonicalization ran only
after a successful reasoner process.

The first production attempts for 10621, 10860 and 1194 used a workstation
binary linked against GLIBC 2.39, which the IBEX image does not provide. Those
pre-execution errors remain in the evidence as `km_production_*` and are not
reasoning results. The decisive reruns use the compatible pinned c229 binary
and are labelled `km_production_c229_*`.

For 3524 and 15703, the standard ORE local-name signature is not injective.
Generated class IRIs contain another full IRI after a slash, so many different
classes share a final fragment. Validation therefore used the committed
[`fingerprint_tail_fulliri.py`](fingerprint_tail_fulliri.py), which preserves
full IRIs, condenses strongly connected components, computes exact transitive
closure with component bitsets and hashes the sorted relation.

For 4669, full HermiT classification does not finish in 240 seconds. The
committed [`SatisfiabilityOracle.java`](../../../oracle/SatisfiabilityOracle.java)
loads the full ontology and asks HermiT directly about one full-IRI class. Every
query has its own timeout and memory cap. Sanity queries return
`owl:Nothing = false` and `owl:Thing = true`.

After the `#Thing` bug was identified, job 49082588 streamed over all 912 files
present in the IBEX corpus directory and intersected its findings with the
592-row benchmark registry. Five registry ontologies declare a non-OWL class
whose short name is `Thing` or `Nothing`: 3524, 4669, 7581, 13503 and 15703.
The audit localized the source-name hazard. The identity-safe fix was then
validated directly on 3524, 13503, 15703 and 7581. Ontology 4669 remains
represented by its separately disproved retained outputs; no fixed 4669 route
is claimed here.

The completed job list is in
[`evidence/direct-validation/ibex-jobs.tsv`](evidence/direct-validation/ibex-jobs.tsv).

## 2669 and 15516: validated solutions

### Route

```bash
env KM_HT_RULES=1 "$KM_BIN" classify "$ORE_CORPUS/ore_ont_2669.owl"
env KM_HT_RULES=1 "$KM_BIN" classify "$ORE_CORPUS/ore_ont_15516.owl"
```

Fresh IBEX results are:

| Ontology | KM wall / peak | HermiT core wall / peak | Canonical result |
|---|---:|---:|---|
| 2669 | 0.1177 s / 15.31 MB | 0.9251 s / 194.98 MB | inconsistent, SHA-256 `3c48c283...` |
| 15516 | 0.1187 s / 15.94 MB | 0.8642 s / 188.67 MB | inconsistent, SHA-256 `3c48c283...` |

The delta-minimized subsets contain a contradiction independent of their
rules: `salary` is forced into both disjoint database-attribute classes. An
inconsistent subset proves the full ontology inconsistent. Konclude cannot
parse the original `DLSafeRule` syntax, so the stored empty classifications are
not reasoning results.

These two adjudicated routes and the three source-symbol repairs below passed
direct semantic validation.

## 3524 and 15703: told subsumptions restored

### Route

```bash
env \
  KM_TRIGGER_ABSORB=1 \
  KM_KEEP_CHAIN_AXIOMS=1 \
  KM_BRIDGE_PROBE_BUDGET_S=30 \
  KM_BRIDGE_RETRY_ROUNDS=0 \
  KM_HT_SATURATION_BUDGET_S=180 \
  KM_HT_MEM_GB=18 \
  KM_PAR_MEM_GB=18 \
  KM_THREADS=16 \
  "$KM_BIN" classify "$ORE_CORPUS/ore_ont_3524.owl"
```

Use the same environment for 15703. The fixed executable and its SHA-256 are
recorded in the TSV.

### Before and after the fix

| Ontology / reasoner | Wall (s) | Peak (MB) | Full-IRI pairs | Taxonomy SHA-256 |
|---|---:|---:|---:|---|
| 3524 KM before fix | 22.5233 | 4391.97 | 1,481,076 | `1c78a2a01f8b7ba9868cd59a443a9c9dea9a8acb21eb794f746065d423e9ce47` |
| 3524 KM fixed | 35.8973 | 4591.72 | 1,604,386 | `090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a` |
| 3524 Konclude | 19.6109 | 4307.32 | 1,604,386 | `090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a` |
| 3524 ELK | 7.8041 | 2697.33 | 1,604,386 | `090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a` |
| 15703 KM before fix | 20.2774 | 4055.16 | 1,481,076 | `1c78a2a01f8b7ba9868cd59a443a9c9dea9a8acb21eb794f746065d423e9ce47` |
| 15703 KM fixed | 24.4077 | 4347.40 | 1,604,386 | `090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a` |
| 15703 Konclude | 17.8164 | 3763.18 | 1,604,386 | `090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a` |
| 15703 ELK | 6.4018 | 2437.21 | 1,604,386 | `090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a` |

Konclude and ELK independently return byte-identical full-IRI node
fingerprints for both ontologies. Before the fix, KM was missing 123,310 strict
pairs in each. Every missing strict pair had this superclass:

```text
http://purl.obolibrary.org/obo/
BFO_0000050_some_http://www.w3.org/2002/07/owl#Thing
```

These are told axioms, so no external oracle is required to establish the
omission. For example:

```text
SubClassOf(
  <http://phenoscape.org/not_has_part/http://purl.obolibrary.org/obo/BFO_0000001>
  <http://purl.obolibrary.org/obo/BFO_0000050_some_http://www.w3.org/2002/07/owl#Thing>)
```

The post-fix dedicated validator sees all 123,311 told occurrences in 3524 and
all 123,310 in 15703. One 3524 occurrence is reflexive and is intentionally
absent from the public non-reflexive taxonomy. All 123,310 strict target edges
are present in both outputs.

### Cause and fix

Before the fix, [`short_base`](../../../engine/src/frontend/iri.rs) took the
fragment after the final `#`, so the legal generated class IRI above received
the internal name `Thing`. [`cls`](../../../engine/src/frontend/parse.rs) then
treated either `owl:Thing` or bare `Thing` as OWL top. The told superclass was
collapsed to top and disappeared from KM's public taxonomy.

The frontend now recognizes top and bottom only from the actual OWL source
IRIs. Legal source names with reserved spellings receive collision-safe
`km_src_*` internal names, while the inverse IRI map restores their exact full
IRIs in output. Both route rows are now `exact_gold`.

## Source-IRI collision audit: 7581 remains exact, 13503 is repaired

The same source scan found two collision-bearing rows that had been recorded as
`exact_gold`.

Ontology 7581 declares the nested class
`BFO_0000050_some_http://www.w3.org/2002/07/owl#Thing`. Its fresh production
run with the fix completed in 19.2328 seconds at 4654.28 MB. When KM and Konclude are
fingerprinted over the same source declaration universe, both return exactly
1,246,911 full-IRI pairs, zero UNSAT classes and taxonomy SHA-256
`27a29aab966ffea74df4aa09c0520545f5908c9fc8e3fc5d10cd3e027b9118d4`.
Ontology 7581 remains `exact_gold` with this stronger evidence.

Ontology 13503 declares a different legal source class:

```text
Declaration(Class(<http://www.daml.org/2001/03/daml+oil#Nothing>))
EquivalentClasses(
  <http://www.daml.org/2001/03/daml+oil#Nothing>
  ObjectComplementOf(owl:Thing))
```

The second axiom directly makes that named class unsatisfiable. Fresh Konclude
returns 113 full-IRI pairs and that one UNSAT class. A targeted HermiT query on
the complete ontology independently returns `satisfiable=false`. Before the
fix, KM returned the same 113 ordinary pairs but zero UNSAT classes. Its
local-name signature had appeared exact only because the canonicalizer
conflated the legal class name `Nothing` with `owl:Nothing`.

With identity-safe source symbols, KM returns 113 full-IRI pairs and the same
one named UNSAT class in 0.0627 seconds at 6.47 MB. Its taxonomy SHA-256 is
`1b8fdf730b9cdce8afed1c69c13e782c6c2dde70c42e5f1d2273dcbdb6b1282b`,
exactly Konclude's fingerprint. Ontology 13503 is now `exact_gold`.

## 4669: both completed KM routes are unsound

Fresh outputs reproduce the route disagreement:

| Route | Wall (s) | Peak (MB) | Pairs | UNSAT classes | Signature SHA-256 |
|---|---:|---:|---:|---:|---|
| production | 15.3261 | 3815.15 | 122,830 | 24,634 | `54e2e95d...` |
| `ht_bridge` | 14.2205 | 2178.42 | 122,092 | 24,690 | `4b0c33ff...` |
| `ht_full` | 13.6745 | 2176.71 | 122,092 | 24,690 | `4b0c33ff...` |

The HT routes add exactly 56 UNSAT classes. HermiT answered a direct
satisfiability query for every one of those 56 classes on the full ontology.
All 56 queries completed, all 56 classes are satisfiable, and peak RSS stayed
below 2.3 GiB. The HT answer is therefore unsound.

The production answer is also unsound. A deterministic sample took the first
ten production-UNSAT classes. HermiT proved eight of them satisfiable; two
queries remained inconclusive because they timed out. Seven proofs came from
job 49076590 and `GO_0000006` completed independently in job 49075857. One
counterexample is sufficient to refute the production output, and eight were
retained.

Full HermiT and Konclude classification both time out at 240 seconds, so there
is not yet a complete authoritative taxonomy for 4669. Direct class queries do
settle the reported UNSAT witnesses. No successful existing 4669 route is a
valid solution.

## 10621: historical diagnosis before the final `ht_bridge` closure

The seven-axiom core committed under
[`results/contested-cores`](../../contested-cores/) correctly proves that
`Zone_of_cell` is unsatisfiable: it inherits `has_mass=true`, is constrained by
`has_mass=false`, and `has_mass` is functional.

The earlier claim that the current IBEX Konclude gold omits this result was
wrong. Fresh isolated Konclude classification completed in 13.8773 seconds at
3245.41 MB and returned 70,827 pairs plus 33,433 unsatisfiable classes,
including `Zone_of_cell`. Its canonical lines are exactly equal to the stored
IBEX gold. The files differ only by a final newline.

KM still has no complete route:

- the pinned production binary times out at 240.0573 seconds and 5863.76 MB;
- direct CB reaches its internal cap at 192.1087 seconds and 3660.30 MB;
- full HermiT classification times out at 240 seconds.

Focused root tests localize the KM timeout. `owl:Thing` and `Zone_of_cell`
complete together in about 1.18 seconds. In the first 64 independently limited
roots, all 55 gold-UNSAT roots time out at 30 seconds, while all 9 satisfiable
roots finish. A 20,000-message trace has 18,739 `Pred` messages, 1,261 `Succ`
messages, 96 successor contexts and 31,426 worked-off clauses. Clause insertion
uses 7.143 of 8.382 traced seconds and grows superlinearly. The bottleneck is
repeated hard bottom-root saturation and clause-set maintenance over the
inverse-role, cardinality and functional-datatype closure.

A sound global bottom prepass finds 33,248 of the 33,433 gold-UNSAT classes,
with zero false positives, in 2.30 seconds at 164 MB. Separately, ELK returns
480,723 pairs and no UNSAT block. Every one of its 409,897 pairs beyond gold has
a gold-UNSAT subject. Using the authoritative UNSAT set as an audit-only filter
leaves 70,826 of 70,827 gold pairs, missing only
`Flagellum ⊑ Organ_part`.

These were validated projections, not a complete KM route. The implementable
plan is a one-time global bottom prepass, certified EL/Horn bulk classification,
then complete reasoning for the 185 complex-bottom classes missed by the
prepass and the tiny non-EL taxonomy residue. Until that composition produces
and validates all 70,827 pairs and 33,433 UNSAT classes, it cannot close the
ontology. The seven-axiom core validates one consequence but cannot stand in
for a full taxonomy. The later capsule-10 `ht_bridge` run does produce and
validate that complete taxonomy; its source-bound record is documented in
`../2026-07-21-route-confirmation/TARGETED-VALIDATION.md`.

## 10860: unsupported rules and live disjunction

The production route exits with the intentional unsupported-feature status:

```text
DL-safe rules: parsed 13 of 17; atom/head unsupported
```

Four rules contain data-property or SWRL built-in atoms that KM cannot
translate soundly. Bypassing the route gate does not reveal a solution. The
single-thread CB path reaches its internal cap after 190.1295 seconds at only
46.67 MB. HermiT rejects the feature combination, and Konclude exits with code
139.

This ontology needs both sound semantics for the four unsupported rule atoms
and convergent reasoning for the live universal-plus-disjunction fragment.
Dropping the rules would classify a weaker ontology and is not an acceptable
route.

## 1194: 20 GiB resource wall

Fresh direct runs confirm the retained diagnosis:

| Reasoner / route | Result | Wall (s) | Peak (MB) |
|---|---|---:|---:|
| KM production | memory limit | 68.8887 | 20482.44 |
| KM `ht_bridge` | memory limit | 75.8151 | 20488.79 |
| Konclude | memory limit | 42.5585 | 20501.72 |
| HermiT | timeout | 240.0551 | 7801.68 |

Ontology 1194 has a 221,086-assertion ABox, 18,055 individuals and more than a
million normalized clauses. Existing complete routes materialize too much
successor, context and per-individual closure state. ELK can return an answer,
but SRIQ is outside its complete profile, so that answer is not an oracle.

No tested route solves 1194 within the benchmark contract.

## Evidence map

- One-row result per tail ontology:
  [`validation-summary.tsv`](evidence/direct-validation/validation-summary.tsv)
- Per-run command, binary hash and resource metadata:
  [`evidence/direct-validation/results/`](evidence/direct-validation/results/)
- Pre-fix full-IRI fingerprints for 3524 and 15703: each reasoner's
  `fulliri.json` in that results tree
- Post-fix full-IRI fingerprints: `fulliri-source.json` in each
  `km_special_iri_fix_*` result directory
- Told-axiom preservation checks: each fixed giant KM result's
  `told-target-validation.json`
- All 56 HT disagreement queries:
  [`4669-satisfiability/`](evidence/direct-validation/4669-satisfiability/)
- Production UNSAT sample and HermiT sanity controls:
  [`4669-production-unsat-sample/`](evidence/direct-validation/4669-production-unsat-sample/)
  and [`4669-hermit-sanity/`](evidence/direct-validation/4669-hermit-sanity/)
- Current 10621 gold comparison:
  [`ore_ont_10621-gold-compare.json`](evidence/direct-validation/ore_ont_10621-gold-compare.json)
- Source collision audit and its registry intersection:
  [`special-iri-audit/`](evidence/direct-validation/special-iri-audit/) and
  [`special-iri-audit-summary.tsv`](evidence/direct-validation/special-iri-audit-summary.tsv)
- Full-IRI 7581/13503 references: `fulliri-source.json` under each
  `*_fulliri_audit_*` result directory, plus the targeted
  [`13503-satisfiability/`](evidence/direct-validation/13503-satisfiability/)
- Fixed-binary build and test log:
  [`special-iri-fix-build-49086702.log`](evidence/direct-validation/special-iri-fix-build-49086702.log)
- Per-ontology route registry:
  [`ontology-solve-routes.tsv`](ontology-solve-routes.tsv)
