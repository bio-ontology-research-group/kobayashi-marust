# KM 1.7.0 release notes

Not yet released (date: unreleased). Numbers marked `[[TBD: ...]]` are not
final. They are filled in from the release gate. Numbers marked
"preliminary" come from a build before the last speed work.

## What changes

KM 1.7.0 widens what KM answers, brings the Protégé plugin close to HermiT,
speeds up classification, and fixes wrong answers. The goals and the work
packages are in `docs/V1.7.0-PLAN.md`.

Read `docs/ERRATA-1.6.5.md` first if you use an earlier release. Releases
v1.5.1 to v1.6.5 can miss an inconsistency or unsatisfiable classes on some
inputs. KM 1.7.0 fixes this.

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
  - Final run against HermiT 1.4.3.456 (`docs/V1.7.0-PARITY-FINAL.md`, KM
    build at `1106b555`): of 545,108 compared calls, 2,106 differ. I decided
    each by the OWL 2 direct semantics. KM is right in 2,102 and HermiT in
    4. The 4 come from two causes: a role assertion that follows from a role
    chain through an anonymous individual, and empty value sets after an
    interrupted property classification. A later merge (`43beadd0`) fixes
    answers after an interrupted query; I did not re-measure it against
    HermiT. The first cause is open. That run used 51 of the 212
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
- **Inconsistent inputs.** A refutation certificate and a checker proved in
  Lean cover inconsistent inputs. 42 of the 46 inputs on which KM answers
  "inconsistent" are certified (`docs/V1.7.0-INCONSISTENCY-CERT.md`). Four
  stay open (`ore_ont_1123`, `4141`, `8445`, `10860`).
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

Preliminary (build `ebe741b4`, before later speed work). Ibex, 585 held-out
inputs, one core, 240 s limit, same day (2026-11-21):

| | solved | mean, common 577 | median, common 577 | median peak memory |
|---|---:|---:|---:|---:|
| KM (plain build, `ebe741b4`) | 579 | 1.94 s | 0.146 s | 27.2 MiB |
| Konclude | 578 | 2.00 s | 0.167 s | 47.5 MiB |

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
  6.3 s to 45.8 s. Its earlier speed came from the unsound confirmation
  described in the errata. Recovery is in progress; status at release:
  `[[TBD: ore_ont_12451 time at the release commit]]`.
- 20cddc6d (binary hypertableau hand-off, 1 to 3 percent) stays on its
  branch and is not in this release.

### Fixed wrong answers

These are answers that were too weak (a missed inconsistency, unsatisfiable
class or subsumption). See `docs/ERRATA-1.6.5.md` for the earlier releases.

- A declined saturation-cache attempt confirmed a label that it had not
  covered. On inputs where merges make an individual its own successor and
  a functional data property has two values, KM reported "consistent"
  where HermiT reports "inconsistent" (`19b80195`, `af790502`).
- The functional merge kept one polarity per concept, so two successors
  with `B, ¬C` and `¬B, C` lost their clash. A class that needs both was
  reported satisfiable (`8a34a1e3`).
- Optimized blocking read only the reapply queue of the blocker, so a
  blocker whose restrictions were never applied blocked a successor and
  subsumptions were lost (`c11e5db6`). A blocking-focused fuzz found 22
  wrong rows in 1,200 cases before the fix and none after it.
- `--different` rows depended on hash order.
- Plugin: after an interrupted query, later queries returned empty sets or
  stayed refused; they now run fresh (`43beadd0`).
- Checker producer: Lean-quoted literals with an escaped quote were cut
  (`76ba207d`).

Differential checks on the branch: 4,920 standard and 2,400 blocking
random cases agree with HermiT after the last fix. Three of the standard
cases were also wrong on the development line before the fix. The pool gate shows 0 answer
differences on 1,696 solved inputs.

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

- Completeness is on checked-model terms (above). The engine does not carry
  a completeness proof for every OWL 2 DL input. Nominal inputs outside the
  C2a fragment (68 pool inputs in the census) have checked models only.
- Hint coverage is partial: some inputs have no model, a partial model, or a
  model the checker cannot check within the budget.
- Four inconsistent inputs stay uncertified (`ore_ont_1123`, `4141`,
  `8445`, `10860`).
- Plugin: parity run covered 51 of 212 strict-rejected inputs. Class
  expression queries with `ObjectMinCardinality` over a non-simple role are
  refused (OWL 2 DL forbids them; HermiT accepts them). Some DL-safe rule
  cases decline for `getDisjointDataProperties`. On `ore_ont_3708` and
  `ore_ont_5033` the data-property phase took 296 s in an earlier run. A
  role assertion that follows from a chain through an anonymous individual
  is not returned by `getObjectPropertyValues`.
- Part of the plugin's answers are still computed in Java (class (b)
  reductions in `docs/V1.7.0-PLUGIN-REDUCTIONS.md`). They are covered by
  randomized differential tests, not by the Lean proofs.
- The finite-cover route answers only covers of at most four individuals,
  and gives no certificate or model.
- Model export declines on some inputs, and the exported model does not
  always yield a checked model for every row.
- Two open timeouts from the parity run (`km_slow_f9001_79.ofn` and
  `km_slow_f9002_65.ofn` in `scratch/parity2/repro/`); `ore_ont_9151` class
  tests (`docs/V1.7.0-SPEED.md`, c17).
- macOS and Windows: as in v1.6.3, the plugin was tested inside Protégé on
  Linux only, and the macOS binaries are not signed.

## Assets

`[[TBD: asset names and checksums]]` (the Protégé 5 and 6 jars, and the km
executables for the five platforms, as in v1.6.5).
