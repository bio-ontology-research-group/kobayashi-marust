# KM 1.7.0 release notes

This is KM 1.7.0. Three release candidates were published first (see
"Release candidates"). The numbers below were measured on the third
candidate (`c63f3a44`) or on its parent `07fba7aa`, as each line says. The
lines marked "final" were measured on `e6257322`, which differs from the
tagged commit by documentation only.

### Items measured on the final commit

Five items come from the final commit.

- Release date: 2026-11-25
- Release chain on the final commit (gate test counts, Rust step, Java
  suite, axiom audit): on `e6257322`: five Lean gates pass (elc 9, routing 311, ht 254, cb 44, rules 40 tests; 0 `sorryAx`); axiom audit over 66,891 constants finds only `propext`, `Classical.choice`, `Quot.sound`; Rust step 3,818 passed, 0 failed; checker tests 57 of 57; Java 219 of 219. One Java process test (`stubbornChildIsForcedWhileSupervisorCanStillReap`) failed in 1 of 5 extra repeat runs, as it did on `07fba7aa` (see "Known limits").
- Held-out timing table against Konclude v0.7.0-1138, measured on the final
  binary (the table below is the final one): done, see "Speed and memory".
- Checkers-on pool counts on the final commit (the counts below are from
  `07fba7aa`): on `e6257322`, 1,696 solved, 1,618 fully certified, 78 solved
  but not certified (67 declined, 11 timed out), 12 unsolved, 0 rejected.
  The difference of 3 to `07fba7aa` is in checker time and memory limits
  (three hint checks timed out at 240 s, one producer failed, one input
  newly certified); no answer changed.
- Assets (names and checksums): listed on the GitHub release page, with a `SHA256SUMS` file; the Linux x86_64 PGO binary has sha256 `80819d30889401e680a11b1c6352fbf735f5d25700b6a405f5af04da5dfdfec3`

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
  runs solved 1,696 inputs, with the same answers at every gate. The second
  release candidate keeps that count (240 s, one core).
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
    through anonymous individuals (`b6cb3438`) came after that run.
  - Release candidate runs (`par4/PARITY4.md` on rc1, `par5/PARITY5.md` on
    rc2, `par6/PARITY6.md` on rc3). On rc3: 349 ontologies, 554,406
    comparable calls equal, KM right in 2,153 differing calls, HermiT right
    in 0, 46 declined. KM timeouts on the comparable sets: 1,573 at
    `800fc8f6` (before the complete r-Succ rule), 11,091 on rc1, 3,617 on
    rc2, 2,211 on rc3. Plugin calls that answered at `800fc8f6` and were
    lost on the lost list: 61,688 on rc1, 42,686 on rc2, 673 on rc3 (627 of
    them on one synthetic input). The one call where HermiT was right on
    rc2, `ore_ont_3205` (a negative data property assertion), was a
    regression from the n-ary singleton rule; it is fixed (`c616d963`).
  - Earlier run (`docs/V1.7.0-PARITY-FINAL.md`, KM
    build at `1106b555`): of 545,108 compared calls, 2,106 differ. Each
    difference was decided by the OWL 2 direct semantics. KM is right in 2,102 and HermiT in
    4. The 4 come from two causes: a role assertion that follows from a role
    chain through an anonymous individual, and empty value sets after an
    interrupted property classification. A later merge (`43beadd0`) fixes
    answers after an interrupted query. The first cause is fixed after that
    run (`b6cb3438`) and tested on 3,300 cases. That run used 51 of the 212
    inputs that strict mode rejects.
  - In that run KM did not answer 3,511 calls that HermiT answered
    (timeouts) and refused or failed 46 more.
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
- **Full IRIs in output.** `km classify --iris full` (or `KM_IRIS=full`)
  prints every entity as its full IRI, for every input syntax and in every
  output row. The default (`--iris source`) is unchanged and may change in a
  later version. See `docs/INPUT-FORMATS.md`, "Entity names in output"
  (GitHub issue #8, reported by Michel Dumontier).
- **Plugin runs.** No `km` process survives the end of a query, whichever
  way it ends (normal end, time out, interrupt, dispose, JVM exit). A batch
  query that hits the reasoner's time out keeps running in the background
  and serves later calls; `interrupt()` discards it and returns after the
  stopped runs have cleaned up. Temporary files are named
  `kmarust-<pid>-...` in `java.io.tmpdir` and are removed when the query
  ends. See `protege/README.md`.
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
  disagreement with KM. The checkers-on run below gives the current count.
- **Checkers-on run.** One pool run with the Lean checkers switched on, on
  `07fba7aa` (the parent of the third candidate; counts in
  `scratch/certcount/results-rc3/summary.txt`): 1,696 inputs solved, 1,621
  fully certified (a hint or refutation accepted, no checker rejected), 75
  solved but not certified (65 declined, 10 timed out), 12 unsolved, 0
  rejected. Three inputs (`ore_ont_13483`, `13690`, `3562`) give a
  different answer hash under the checkers. The cause is a different
  listing of subsumption edges of unsatisfiable classes between the
  in-process engine and the forked worker. The sets of unsatisfiable classes
  are the same, and so is the closure for satisfiable classes. An earlier
  run (`bbe67385`) took 1.7 times the plain wall time in total (median ratio
  1.13; 1.01 on inputs over 5 s) and 1.5 times the summed peak memory
  (median ratio 1.01).
- **Rule ontologies under certificate modes.** The ground-rule reduction
  has no Lean certificate. KM runs the older rules route first (which has
  one) only when a rules certificate is requested by name, with a 30 s
  budget (`KM_RULES_FIRST_BUDGET_S`). Under `KM_LEAN_CHECKERS` a rule
  ontology takes the default path and records a `cannot_check` event.
  Wiring `rules-cert-check` into `KM_LEAN_CHECKERS` is open and planned
  after the release (`docs/V1.7.0-RULES-SHOIQ.md`).
- **Inconsistent inputs.** A refutation certificate and a checker proved in
  Lean cover inconsistent inputs. 42 of the 46 inputs on which KM answers
  "inconsistent" were certified (`docs/V1.7.0-INCONSISTENCY-CERT.md`); the
  checkers-on run on `07fba7aa` certifies 43 of 46. Of the four that stayed
  open (`ore_ont_1123`, `4141`, `8445`, `10860`), `4141` is certified, and
  `1123`, `8445` and `10860` are not (all three declined).
- **Proof scope.** According to the merge messages, completeness is proved
  on OWL EL, ALC and SHI (v1.6.3), and the v1.7.0 work adds SHIQ at the
  normal-form level, knowledge bases with an ABox, datatypes and the
  nominal fragment C2a, with role features. Inputs outside these parts have
  checked-model certificates only. The Lean gate results are under "Checks
  for this release".
- Soundness and completeness claims hold for the Lean statements, not for
  the Rust code. Tests, differential runs and the checkers compare the Rust
  answers with the statements.

### Speed and memory

Ibex, 585 held-out inputs, one core, 240 s limit. Final PGO binary (built
from `e6257322`, sha256 `80819d30...`), Konclude v0.7.0-1138 and KM v1.6.5 in
the same run. Mean and median time are over the 577 inputs that KM 1.7.0 and
Konclude both solve; memory is the peak.

| | solved | mean time | median time | median memory | mean memory |
|---|---:|---:|---:|---:|---:|
| KM 1.7.0 | 579 | 1.70 s | 0.141 s | 31.2 MiB | 167 MiB |
| Konclude | 578 | 2.06 s | 0.169 s | 48.5 MiB | 256 MiB |
| KM v1.6.5 (PGO release binary; over the 575 inputs all three solve) | 576 | 3.27 s | 0.160 s | 71.8 MiB | 330 MiB |

KM is faster on 335 of the 577 common inputs and smaller on 462. On the
575 inputs that all three solve, KM 1.7.0 takes 1.48 s mean and 0.140 s
median, Konclude 1.92 s and 0.167 s. The first candidate was faster in the
mean (1.36 s): the complete r-Succ rule added after it costs time on a few
inputs (`ore_ont_762` takes 49 s, Konclude 9 s). The PGO to plain time ratio
is 0.92 on 196 pool inputs with identical answers. On the
pool, the gates for rc2 and rc3 show no time or memory regression against
the previous candidate.

### All baseline reasoners (full pool)

KM 1.7.0 (plain build of `e6257322`, pool run of 1,708 valid ORE 2015
inputs, one core, 240 s) against the stored results of the comparative run
of October 2026 (same node type and limits; results in
`v145-comparative-20261004`). A baseline counts an input as solved when its
answer agrees with another full OWL DL reasoner. Times and memory are over
the inputs that KM 1.7.0 and the baseline both solve. The baselines were not
run again for this release.

| Reasoner | solved | mean time: KM / baseline | median time: KM / baseline | median memory: KM / baseline |
|---|---:|---:|---:|---:|
| KM 1.7.0 | 1,696 | | | |
| Konclude 0.7.0 | 1,655 | 1.01 s / 2.92 s | 0.11 s / 0.27 s | 26 / 47 MiB |
| HermiT | 1,539 | 0.59 s / 15.7 s | 0.09 s / 4.97 s | 24 / 168 MiB |
| ELK | 1,411 | 1.05 s / 12.0 s | 0.09 s / 4.78 s | 24 / 165 MiB |
| Openllet | 1,402 | 0.38 s / 16.3 s | 0.07 s / 4.89 s | 21 / 171 MiB |
| Whelk | 1,380 | 0.86 s / 17.7 s | 0.09 s / 6.20 s | 23 / 194 MiB |
| RustDL 0.4.28 | 1,212 | 0.83 s / 5.14 s | 0.09 s / 0.33 s | 23 / 25 MiB |
| JFact | 1,101 | 0.17 s / 17.4 s | 0.05 s / 5.21 s | 17 / 172 MiB |
| Sequoia | 629 | 0.69 s / 18.7 s | 0.06 s / 7.38 s | 18 / 254 MiB |

KM 1.7.0 solves every input that ELK, JFact, RustDL and Sequoia solve, and
all but one of the inputs that each of Konclude, HermiT, Openllet and Whelk
solves. Its mean memory is also lower than each baseline's on the common
inputs. Against RustDL the memory gap is small: KM uses less on 546 of the
1,212 common inputs.

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
  described in the errata.
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
- Two TBox sweeps of 20,200 cases each, on 12 routes. The first found the
  n-ary, cardinality, substitute-chain and HT cardinality errors. The
  second left only errors on the nominal routes; those are fixed, and the
  46-case acceptance set for them passes (before the fix the development
  head was wrong on all 46 on some route and on 18 on the automatic route;
  at the head 0 are wrong and 3 stay silent on the automatic route).
- 5,000 targeted TBox fuzz cases on 8 routes against HermiT after the
  transitive fix: 0 KM errors (54 per CB route before).
- 4,920 standard and 2,400 blocking random cases agree with HermiT.
- On `caf9c171` and `07fba7aa`: two TBox sweeps of 20,200 cases on
  12 routes with 0 unsound and 0 incomplete answers on every route, and the
  64,000-case campaign and the targeted nominal families with 0 wrong
  answers.
- Every merge passed a paired pool gate on Ibex: 0 answer differences on
  the 1,696 solved inputs.
- Plugin: 477,120 calls against HermiT on 3,300 cases, 383 missed rows
  before the anonymous-individual fix and 1 after (a CB-route subsumption
  miss, open). Re-run the Java suite in the release chain.

Upstream Konclude v0.7.0-1138 shows the functional-merge defect
(`case3_c3min.ofn`, confirmed by the supervisor). On the value-merge input
(`value-merge-singleton.ofn`) it gives the same wrong answer, `A`
satisfiable; we did not establish the cause there. See the errata.

Oracle note: HermiT's `isEntailed` was wrong on some inputs, so the
campaigns used HermiT's own consistency test as the oracle. On a few
datatype cases and one role-equivalence case HermiT is wrong there too. The
hand proofs are in the agents' reports (for `r9600_0013`:
`scratch/chainanon/HANDBACK-trans.md`).

## Release candidates

Three pre-releases were published. The texts below follow their GitHub
release notes.

- **v1.7.0-rc1** (`caf9c171`). Known issues: inputs that combine nominals
  with inverse properties, the universal property or data values can be much
  slower than in v1.6.5 or give no answer in time (given answers are
  correct); with `KM_LEAN_CHECKERS` set, three rule ontologies
  (`ore_ont_2526`, `6615`, `15063`) time out; the commit does not compile on
  macOS and Windows, so rc1 has only a Linux x86_64 binary and no plugin
  jars.
- **v1.7.0-rc2** (`9e6761f3`). Builds on macOS and Windows; plugin jars for
  Protégé 5 and 6. Less slowdown on nominal inputs (about 330 of 503 test
  cases that gave no answer on rc1 answer again); rule ontologies take the
  default path under `KM_LEAN_CHECKERS`. Known issues: a wrong answer
  (regression since rc1) when one individual has two values of a functional
  data property and another individual also has a value (shown in the plugin
  as `isEntailed` false for a negative data property assertion that holds;
  `ore_ont_3205`; v1.6.5 not affected); plugin queries slower on inputs with
  nominals (about 60 ORE ontologies); `getDataPropertyValues` declined on
  some ontologies with integer facet restrictions; no answer in time on
  about 0.4 percent more class-level test cases; the plugin jars carry the
  version 1.7.0 internally.
- **v1.7.0-rc3** (`c63f3a44`). Fixes the wrong answer above, sends labels of
  individuals only on demand (with the Lean module `CBRSuccDemand`), fixes
  `getDataPropertyValues` next to facets, cleans up plugin processes and
  files, adds `--iris full`. Known issues: synthetic inputs in which many
  individuals may equal the same nominal can be much slower than in v1.6.5,
  and some property-value queries on them time out (627 of the 673 lost
  calls on one small ontology); no answer within 60 s on about 0.25 percent
  more class-level cases than before the complete rule (48 of 20,200 per
  sweep); a `km` started by a JVM killed with SIGKILL runs to its own time
  limit; 75 of 1,696 pool answers are not fully checked with the checkers on;
  the plugin jars carry the version 1.7.0 internally.

## Fixed since rc2

- Wrong answer in rc1 and rc2 only (not in v1.6.5): one individual with two
  values of a functional data property, when another individual also has a
  value, was reported consistent. The n-ary singleton rule (`bfb7be93`) made
  the clash axiom `DifferentIndividuals(b b)` vacuous. The projection now
  writes `ClassAssertion(owl:Nothing b)` (`c616d963`, `1845fd9f`).
- Plugin: `getDataPropertyValues` next to integer facet restrictions
  answers again (402 declined calls on `ore_ont_2548`, `13700`, `9662`).
- Plugin: no orphaned km processes; batch runs survive a per-call time out,
  `interrupt()` discards them and returns after cleanup; a stopped batch
  always ends its call with the stop (`39f1d6b4`, `ad1411b3`).
- Engine: demand-driven r-Succ offers (`7616d8b7`) with the Lean module
  `CBRSuccDemand`.
- `km classify --iris full` (`2f77686f`).

## Checks for this release

Release chain on Ibex for the parent commit `07fba7aa` of the third
candidate (pinned rustc 1.95.0, Lean 4.30.0-rc2; receipts
`gates.json`, `gate-*.json`, `full-rust.json`, `java-receipt.json`
attached to the candidate release). The third candidate adds only the plugin
interrupt and cleanup fix and the `--iris` option; default output is
byte-identical on 200 pool inputs.

- Five Lean gates pass with real checkers: elc 9, routing 311, ht 254, cb
  44 and rules 40 tests, 0 failures, 0 `sorryAx`. The CB gate audits the
  theorem `certifiedCBDeferredLabelUnread`. The whole-library axiom audit
  (66,756 constants on rc1; clean on rc2) finds only `propext`,
  `Classical.choice` and `Quot.sound`.
- Official Rust step: 3,810 passed, 0 failed, 12 ignored. The plain
  `cargo test` of the library fails 21 tests that need the built Lean
  checkers; all integration targets pass.
- Java: 219 tests, 0 failures, 0 errors. The interrupt fix was also run 20
  times as the full Java suite on two cores, all green.
- GitHub build of the third candidate: `km` for Linux x86_64 and aarch64,
  macOS x86_64 and aarch64 and Windows x86_64; both plugin jars built,
  tested and installed in stock Protégé.
- PGO build with rustc 1.95.0: the PGO to plain time ratio is 0.92 on 196
  pool inputs with identical answers.
- Pool (1,708 inputs, 240 s, one core): 1,696 solved, with answers
  identical to every earlier gate.
- Differential testing against HermiT: two sweeps of 20,200 class-level
  cases on 12 routes (0 unsound, 0 incomplete on every route), 5,000 role
  cases, 3,300 cases with individuals (command line and plugin), a
  64,000-case campaign and targeted families: no wrong KM answer. The
  automatic route gives no answer on 176 and 197 of 20,200 cases in the two
  rounds (129 and 151 before the complete r-Succ rule).

The final commit repeats the release chain (see "Open items"); the Lean gates run once more on the tagged commit itself.

## Known limits

- The complete r-Succ rule costs time on some nominal inputs. Demand-driven
  offers (`7616d8b7`, `docs/NOMINALS-CB.md` 14) removed most of it:
  of 503 TBox sweep cases that had gone silent on rc1, 407 answer again;
  the `ore_ont_13584` data-value batch takes 1.6 s (56 s on rc2). The cost that stays is on synthetic inputs where many
  individuals may equal the same nominal (the `f9001` family; one probe
  1.2 s before the rule, over 120 s now) and on two
  `--realize --values --different` examples (about 30 s to about 170 s).
  The acceptance set of 46 hard nominal cases is unchanged: right on all
  four routes for 44, wrong on none, and silent on the automatic route for
  1. No pool input is affected. The quick cut that would remove the
  remaining cost is unsound (test `nominal_label_relay`; `docs/NOMINALS-CB.md`
  13.2 and 14.4). The forced nominal routes are exact or silent on a few
  fixtures (`m2058`, `m2197`, `cut_r129_pushback`, `merge_r1646`, the
  universal-role hub with data values).
- Plugin: a one-shot `km classify` or `km explain` started by a JVM that is
  killed with SIGKILL runs to the end of its own time limit. After a JVM
  shutdown with SIGTERM or SIGINT, the plugin stops the km processes.
- Plugin test `stubbornChildIsForcedWhileSupervisorCanStillReap` failed in
  1 of 5 extra repeat runs on Ibex (also on `07fba7aa`). The 219-test Java
  suite itself passes. Open.
- `km classify --lines --realize --top` on `ore_ont_16744` stops after 8 s
  with "pair count exceeds limit" (it timed out before). Plain
  `km classify` answers this input as before.
- With the checkers on, 78 of 1,696 pool answers (75 on `07fba7aa`) are not fully checked
  because a checker declines, or runs out of time or memory. No checker
  rejects an answer.
- `km classify --iris full` is off by default; names in the default output
  are as the input spells them.
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
  others are `ore_ont_1123`, `8445` and `10860`.
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

The Protégé 5 and Protégé 6 plugin jars with bundled executables, `km` for
the five platforms, and the checksum files, as for the release candidates.
Names and checksums are listed under "Open items".
