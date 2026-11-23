# KM 1.7.0 release notes

Not yet released (date: unreleased). Numbers marked `[[TBD: ...]]` are not
final. They are filled in from the release gate. Numbers marked
"preliminary" come from a build before the last speed work.

## What changes

KM 1.7.0 widens what KM answers, brings the Protégé plugin close to HermiT,
speeds up classification, and fixes wrong answers. The goals and the work
packages are in `docs/V1.7.0-PLAN.md`.

Read `docs/ERRATA-1.6.5.md` first if you use an earlier release. Releases
up to v1.6.5 can miss an inconsistency, unsatisfiable classes or
subsumptions on some inputs. KM 1.7.0 fixes the cases we found, with small
reproducers in `docs/errata/1.6.5/`. Two of them (OWL/XML inputs, GitHub
issues #6 and #7) were reported by Michel Dumontier.

### For users

- **OWL 2 DL coverage.** KM answers inputs with nominals, number
  restrictions, inverse and chained roles, `ObjectHasSelf`, keys, datatypes
  and facets, individuals and DL-safe rules. The Protégé plugin and the
  command line handle each of these, and the engine declines (exit 3) what
  it cannot represent. On the 1,708-input ORE pool, the paired release-gate
  runs solved 1,696 inputs. Final count: `[[TBD: pool inputs solved at the
  release commit]]`.
- **More query rows from `km classify`.**
  - `--realize` adds `TYPE a C` and `SAME a b` rows.
  - `--values` adds `VALUE r a b`, every entailed object property assertion
    between named individuals.
  - `--different` adds `DIFFERENT a b`, every entailed pair of different
    named individuals (`a < b`).
  - `--properties` adds the object property hierarchy, domains and ranges;
    `--data-properties` adds the data property hierarchy, empty data
    properties, domains and disjoint data properties; `--top` adds the
    classes equivalent to `owl:Thing`.
  - Rows are read off one classification of the input extended with fresh
    classes. See `docs/PROPERTIES.md` and `docs/V1.7.0-PLAN.md`, section 2.
  - `DIFFERENT` rows now come from the model plan, and no longer depend on
    hash order.
- **HermiT parity in Protégé.** The plugin answers the `OWLReasoner`
  methods that HermiT answers: types, instances, same and different
  individuals, object and data property hierarchies, domains and ranges,
  property values, class expression queries, disjoint classes and
  properties, `isEntailed` for the axiom types, precompute and the meta
  calls. It also follows HermiT's conventions for the interrupt,
  timeout and inconsistent-ontology cases. The plugin builds each answer by
  an exact reduction to km runs on an extended ontology. Some reductions
  still compute part of an answer in Java; the inventory is
  `docs/V1.7.0-PLUGIN-REDUCTIONS.md`.
  - Third run (`/mnt/data1/leechuck/km-work/v170/scratch/par3/PARITY3.md`,
    build `800fc8f6`, the same 3 sets as below): KM and HermiT agree on
    555,041 calls. Of 2,156 differing calls, KM is right in 2,154 and
    HermiT in 2 (the chain through an anonymous individual). The 8,045
    killed calls are gone, and KM timeouts fell from 3,511 to 1,573. No
    answer that was right became wrong. On 100 more strict-rejected inputs,
    KM is right in 510 differing calls and HermiT in none; 467 calls stay
    undecided (KM lists more than HermiT). The plugin fix for values
    through anonymous individuals (`b6cb3438`) came after that run and
    needs a rerun: `[[TBD: parity rerun at the tag]]`.
  - Earlier run (`docs/V1.7.0-PARITY-FINAL.md`, KM
    build at `1106b555`): of 545,108 compared calls, 2,106 differ. I decided
    each by the OWL 2 direct semantics. KM is right in 2,102 and HermiT in
    4. The 4 come from two causes: a role assertion that follows from a role
    chain through an anonymous individual, and empty value sets after an
    interrupted property classification. A later merge (`43beadd0`) fixes
    answers after an interrupted query; I did not re-measure it against
    HermiT. The first cause is fixed after that run (`b6cb3438`) and tested on 3,300
    cases. That run used 51 of the 212
    inputs that strict mode rejects; the rest did not run.
  - KM did not answer 3,511 calls that HermiT answered (timeouts) and
    refused or failed 46 more. Re-run on the release binary:
    `[[TBD: parity rerun at the release binary]]`.
- **Lenient input.** `km classify --lenient` (and the plugin) accepts inputs
  that OWL API and HermiT load in Protégé but that strict OWL 2 DL checking
  rejects, by a source rewrite before reasoning (anonymous individuals in
  `ObjectHasValue`, characters outside RFC 3987 in IRIs, and other cases in
  `docs/V1.7.0-LENIENT-INPUT.md`). KM prints a `LENIENT` row for each
  rewrite. Without the flag, strict mode is unchanged. Of the 1,920 inputs
  in the corpus, 212 are rejected in strict mode.
  `--unknown-datatypes=free` reads datatypes outside the OWL 2 datatype map
  (such as `xsd:date`) as fresh datatypes and their literals as opaque
  values; the default is `strict`. The plugin turns both on, as Protégé does
  for HermiT.
- **Model export.** `km classify --export-model FILE` writes a finite
  model of the input as JSON lines (`km-model-v1`):
  elements with their classes and individuals, object property edges closed
  under the RBox, data values, merged individuals. A budget
  (`--export-model-budget`) can stop the witness search; the file then says
  `"status":"partial"`. Some inputs decline. Without the flag nothing is
  kept and the run costs the same as before. Format and limits:
  `docs/MODEL-EXPORT.md`.
- **Finite-cover route.** An ontology with a cover `⊤ ⊑ {o1, …, ok}` has at
  most `k` elements in every model. Small inputs of this kind took minutes
  with KM and seconds with HermiT. Two changes remove the cost. The CB
  engine now merges every individual into the single element when the
  cover has one individual. A new route (`finite_cover`) decides covers of
  two to four individuals by a SAT search over the at most four elements. It
  declines when a run needs a certificate or a model, with more than four
  cover individuals, with data roles, and beyond fixed size bounds, and the
  other routes then answer. See `docs/V1.7.0-NOMINAL-COVER.md`.
  Checks: paired pool gate, 0 answer differences on 1,696 solved inputs and
  no time or memory flags; 400 fresh cases with the route on and off, every
  differing row decided (old-path timeouts, unsound `DIFFERENT` rows of the
  old path, and HermiT listing errors).
- **Input and output details.** Inverse property operands are read in
  `SubObjectPropertyOf`, `EquivalentObjectProperties`,
  `DisjointObjectProperties` and the property characteristics. DL-safe
  rules accept more atoms (data variables in the body only, nominals,
  inverses, number restrictions, finite built-ins). `km` runs outside a
  source checkout. Each run keeps its temporary files in one directory that
  it removes on every exit path.

### Certificates and what they cover

The claim is about checked models, in the terms of
`docs/V1.7.0-PLAN.md` (sections 17 and 18). It is not a proof that the
engine is complete on every OWL 2 DL input.

- **Positive answers** (a subsumption, a type, an inconsistency) rest on the
  soundness theorem `kmSupervisor_sound`, as in earlier releases.
- **Negative answers** (a non-subsumption, a non-type, consistency) are
  certified when a checker proved in Lean accepts a model of the input that
  shows the answer. The producer `km-hints` builds the model from the KM
  rows, or from `--export-model`. The route is `sroiq-hint`; it needs no
  completeness proof of the reference search.
- **Coverage on the pool.** At the last measurement (`h3d`, branch merge
  `e8b49702`) the checker confirmed every negative row on 1,517 of the 1,708
  pool inputs. The other inputs have rows missing, a model that the checker
  took too long to check, or no model. The rows that were checked had no
  disagreement with KM. Final coverage at the release commit:
  `[[TBD: inputs confirmed full at the release commit]]`.
- **Checkers-on run.** One pool run with the Lean checkers switched on
  (build `bbe67385`; to be re-run at the tag, `[[TBD: checkers-on run at
  the tag]]`): of 1,696 solved inputs, 1,623 are certified (a hint or
  refutation accepted, no checker rejected), 65 solved inputs are not
  certified because a step declined, 8 because a step timed out, and 12
  inputs are unsolved. No checker rejected an answer. The answers equal the
  plain run on 1,693 inputs; three inputs (`ore_ont_13483`, `13690`,
  `3562`) gave a different answer hash in the checkers-on run and I have
  not explained this (`[[TBD: cause of the 3 answer-hash differences in the
  checkers-on run]]`). The checkers-on run takes 1.7 times the wall time of
  the plain run in total (median ratio 1.13; 1.01 on inputs over 5 s) and
  uses 1.5 times the summed peak memory (median ratio 1.01).
- **Inconsistent inputs.** A refutation certificate and a checker proved in
  Lean cover inconsistent inputs. 42 of the 46 inputs on which KM answers
  "inconsistent" were certified (`docs/V1.7.0-INCONSISTENCY-CERT.md`); the
  checkers-on run certifies 43 of 46. Of the four that stayed open
  (`ore_ont_1123`, `4141`, `8445`, `10860`), `4141` is now certified, and
  `1123`, `8445` and `10860` are not (declined; producer timeout; declined).
- **Proof scope.** According to the merge messages, completeness is proved
  on OWL EL, ALC and SHI (v1.6.3), and the v1.7.0 work adds SHIQ at the
  normal-form level, knowledge bases with an ABox, datatypes and the
  nominal fragment C2a, with role features. Inputs outside these parts have
  checked-model certificates only. The fragment list, the Lean files
  and the axiom audit for the tag: `[[TBD: Lean certification result from the
  exact tag: gates, sorry and axiom audit]]`.
- Soundness and completeness claims hold for the Lean statements, not for
  the Rust code. Tests, differential runs and the checkers compare the Rust
  answers with the statements.

### Speed and memory

Preliminary numbers on Ibex, 585 held-out inputs, one core, 240 s limit.
Both rows are from builds before the last fixes. Re-run both at the tag.

| | solved | mean | median | median peak memory |
|---|---:|---:|---:|---:|
| KM, plain build `ebe741b4` (2026-11-21, mean and median on the 577 inputs both solve) | 579 | 1.94 s | 0.146 s | 27.2 MiB |
| Konclude, same day | 578 | 2.00 s | 0.167 s | 47.5 MiB |
| KM at `bbe67385` (comparison on the common inputs) | 579 | 1.37 s | 0.140 s | 33 MiB |
| Konclude, same comparison | 578 | 1.97 s | 0.164 s | 48 MiB |

The two KM rows come from different builds and runs, so they differ in
more than the code. `[[TBD: re-run of both comparisons at the tag]]`.

Final numbers on the release binary: `[[TBD: held-out solved, mean, median
and median memory for KM and Konclude, release binary]]`. Pool numbers:
`[[TBD: pool solved, mean and median against v1.6.5 and the baselines]]`.

What changed in the engine, from the merge messages. Each merge passed a
paired pool gate on Ibex with 0 answer differences on 1,696 solved inputs
and no flagged time or memory regressions, except where noted below.

- Transparent huge pages are off for the process tree, and the supervisor
  returns freed heap pages before it waits on a worker (about 20 to 30 MiB
  per process with huge pages set to `always`).
- Workers start once, without extra `nice` and re-exec steps. Releasing the
  supervisor's code pages while it waits is opt-in.
- Chain consumers (a role chain's super-role used in a restriction) need
  fewer clauses and less memory.
- Hypertableau bridge: core-blocking marking, relaxed told-subclass
  forcing, role-chain membership as a parent-derived bitset, packed
  tested-pair keys, functional object roles as domain concepts (as
  Konclude does), chunked storage for the three large saturation pools,
  smaller successor records, a validated source piped to the front-end
  worker, and one-pass clause decoding.
- EL completion keeps `(context, role)` maps per context; the EL worker
  hand-off is dictionary-coded; workers' answers are read from a whole file.
- Exact nominal-free realization, a cover shortcut and some hypertableau
  speed-ups.
- One regression from the wrong-answer fixes: `ore_ont_12451` goes from
  6.3 s to about 44 s. Its earlier speed came from the unsound confirmation
  described in the errata. Time at the release commit:
  `[[TBD: ore_ont_12451 time at the tag]]`.
- 20cddc6d (binary hypertableau hand-off, 1 to 3 percent) stays on its
  branch and is not in this release.

### Fixed wrong answers

These are answers that were too weak (a missed inconsistency, unsatisfiable
class or subsumption), except where noted. For each item, `docs/ERRATA-1.6.5.md`
says whether v1.6.5 has it, what a user sees, and where the reproducer is.

Present in v1.6.5 (and in earlier releases, as the errata states):

- Saturation cache: a declined cache attempt confirmed a label it had not
  covered; inputs where merges make an individual its own successor and a
  functional data property has two values were reported consistent
  (`19b80195`, `af790502`, `554a72e7`).
- Functional merge: the saturation kept one polarity per concept, so a class
  needing two disjoint fillers of a functional super-role was reported
  satisfiable (`8a34a1e3`).
- Value merges in saturation: `A ⊑ ≥2 d` with `d` limited to one value
  gave `A` satisfiable (`6b5e1613`).
- Universals over transitive roles were applied along one edge only on the
  CB routes, since the first Rust frontend (`a111e343`, `eb04beb3`,
  `d21a49e0`).
- N-ary axioms read their operands by position: `DisjointClasses(B D D)`
  made `D` unsatisfiable. They are now sets, as in the OWL 2 specification
  and the OWL API (`f2710130`, `bfb7be93`). A single remaining operand in
  `DisjointClasses(A A)` makes `A` unsatisfiable, as in Protégé.
- Classes that occur only as a qualified cardinality filler were missing
  from the rows of the HT cardinality routes (`04a49e49`).
- Bridge root label: the root kept the label of the last substitute node but
  not the concepts of the nodes in between (`ee79d91a`).
- HT cardinality number rule: a marker was derived at a node without a
  decision behind it (`4acc762d`, `c6ff52f6`).
- Certified EL arm: a node with an edge to a dead node was not dead in the
  repair pass, so `SUB X Q0` rows were missing (`1f71bc91`).
- Separability certificate with a nominal in a domain or range: the
  automatic route classified the TBox alone and lost subsumptions
  (`482a3458`).
- Nominal CB routes: the labels of an individual were not offered to its
  successors, so inconsistencies and subsumptions were missed on the forced
  `nominals` and `certified_nominals` routes. The automatic route answered
  these through the bridge on the cases we have. r-Succ offers now follow
  the rule of arXiv:1805.01396 (`30c850c4`, `a84969a4`, `9bd68cb6`,
  `24d50930`). The Lean closure is extended to match.
- Rule worker: a self atom `r(x, x)` in a clause body matched any `r` edge,
  so an irreflexive role with a key or a DL-safe rule and one `r` edge
  gave "inconsistent" on the forced rules routes (`b15cf0d8`; the bug dates
  from v0.1).
- Plugin: `getObjectPropertyValues` and `isEntailed` lost a row through an
  anonymous individual (`c1(a4, a4)`); these go to exact probes now
  (`b6cb3438`, `34f9e651`).
- OWL/XML input: full IRIs are written on conversion (GitHub issue #6,
  `df2529cf`); `km features` scans constructs after the conversion to
  functional syntax, so OWL/XML, RDF/XML and Turtle inputs no longer show
  zero constructs (issue #7, `42da1e86`). Reported by Michel Dumontier.
- Source rows keep the source spelling after the numeric normalization
  (`ad777d85`; present at v1.6.5 at least).

Found in the same campaign, with the defects above (also in v1.6.5 or not
tested): the blocking test read only the reapply queue of the blocker
(`c11e5db6`). We did not test whether v1.6.5 shows it.

Not in v1.6.5 (new in the v1.7.0 development, fixed before release): the
`--different` model plan (nine causes, including hash-order dependence,
`DIFFERENT` rows that HermiT does not entail, and merges that skipped
neighbours), the `--data-properties` probe with different ranges
(`550c0b6f`), and the frontend `DataHasValue` pass on forced nominal routes
(`4910d82e`).

Also in this release: with the new defaults the forced routes `tableau` and
`tab_race` no longer exist; they published wrong subsumptions with
`DROPPED 0` on 15 sweep cases and no automatic path reached them
(`62ad6911`). The `km tableau` worker stays.

Evidence:

- A 64,000-case differential campaign against HermiT on Ibex.
- Two TBox sweeps of 20,200 cases each, on 13 routes. The first found the
  n-ary, cardinality, substitute-chain and HT cardinality errors. The
  second left only errors on the nominal routes; those are fixed, and the
  46-case acceptance set for them passes (before the fix the development
  head was wrong on all 46 on some route and on 18 on the automatic route;
  at the head 0 are wrong and 3 stay silent on the automatic route).
- 5,000 targeted TBox fuzz cases on 8 routes against HermiT after the
  transitive fix: 0 KM errors (54 per CB route before).
- 4,920 standard and 2,400 blocking random cases agree with HermiT.
- Every merge passed a paired pool gate on Ibex: 0 answer differences on
  the 1,696 solved inputs.
- Plugin: 477,120 calls against HermiT on 3,300 cases, 383 missed rows
  before the anonymous-individual fix and 1 after (a CB-route subsumption
  miss, open). Re-run the Java suite in the release chain.

Upstream Konclude v0.7.0-1138 shows the functional-merge defect
(`case3_c3min.ofn`, confirmed by the supervisor) and, in our run, the
value-merge defect (`value-merge-singleton.ofn`: it classifies `A` as
satisfiable). See the errata for the table and its limits.

## Checks for this release

PENDING: Ibex certification from the tag (build, Lean gates and axiom
audit, Rust suite, Java and checkers) and the speed and correctness runs:
`[[TBD: certification and gate results at the tag]]`.

Test counts at the release commit: `[[TBD: Rust lib, integration and plugin
test counts and the list of failing tests]]`. Earlier baselines: 21 library
tests failed on development because they need the Lean checker binaries.
At the merge of `43beadd0`, the plugin suite passed 192 of 194; the two
failures were in `NativeProcessTreeTest`, which also fails about 1 run in 6
on development under load. Rerun on the release machine.

## Known limits

- With the complete r-Succ offers, the automatic route gives no answer
  within the time limit on some synthetic nominal inputs that it answered
  before (about 3 to 5 percent of the targeted fuzz cases). No pool input
  is affected (`docs/NOMINALS-CB.md`, 13.2). The forced nominal routes are
  exact-or-silent on a few fixtures (`m2058`, `m2197`, `cut_r129_pushback`,
  `merge_r1646`, the universal-role hub with data values): they either give
  the exact answer or fail closed.
- `ore_ont_12451` takes 44 s where v1.6.5 took 6 s (its speed came from the
  unsound cache confirmation). Three large inputs use 13 to 16 percent more
  memory than before the r-Succ change (`ore_ont_10926`, `1673`, `12128`).
- The forced routes `tableau` and `tab_race` are gone.
- Completeness is on checked-model terms (above). The engine does not carry
  a completeness proof for every OWL 2 DL input. Nominal inputs outside the
  C2a fragment (68 pool inputs in the census) have checked models only.
- Hint coverage is partial: some inputs have no model, a partial model, or a
  model the checker cannot check within the budget.
- Inconsistent inputs: 43 of 46 are certified in the checkers-on run; the
  others are `ore_ont_1123`, `8445` and `10860`. To be re-run at the tag.
- Plugin: the parity runs covered 151 of the 212 strict-rejected inputs
  (51, then 100 more). Class
  expression queries with `ObjectMinCardinality` over a non-simple role are
  refused (OWL 2 DL forbids them; HermiT accepts them). Some DL-safe rule
  cases decline for `getDisjointDataProperties`. On `ore_ont_3708` and
  `ore_ont_5033` the data-property phase took 296 s in an earlier run. One
  CB-route subsumption miss from the 3,300-case plugin run is open.
  `ore_ont_14379` and `ore_ont_3080` still time out in the parity run.
- Part of the plugin's answers are still computed in Java (class (b)
  reductions in `docs/V1.7.0-PLUGIN-REDUCTIONS.md`). They are covered by
  randomized differential tests, not by the Lean proofs.
- The finite-cover route answers only covers of at most four individuals,
  and gives no certificate or model.
- Model export declines on some inputs, and the exported model does not
  always yield a checked model for every row.
- `ore_ont_9151` class
  tests (`docs/V1.7.0-SPEED.md`, c17).
- macOS and Windows: as in v1.6.3, the plugin was tested inside Protégé on
  Linux only, and the macOS binaries are not signed.

## Assets

`[[TBD: asset names and checksums]]` (the Protégé 5 and 6 jars, and the km
executables for the five platforms, as in v1.6.5).
