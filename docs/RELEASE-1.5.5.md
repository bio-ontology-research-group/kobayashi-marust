# KM 1.5.5 release notes

Released 2026-11-09 from commit a4bb4808 (tag `v1.5.5`, the same commit as
`v1.5.5-rc3`). The first candidate (edeb7fff, 2026-11-01) was not released
because it verified fewer held-out inputs than Konclude; the eight days in
between went into the ported Konclude bridge, which now answers 15 of the
16 inputs that candidate lost to Konclude. Every clause of the acceptance
contract `docs/V1.5.5-ACCEPTANCE.md` is met without amendment; the evidence
is recorded there ("Evidence", candidate rc3) and in the campaign log
`docs/V1.5.5-STATUS.md`.

Version 1.5.5 fixes every soundness and completeness defect found since
v1.5.4 in a ten-day differential campaign against HermiT 1.4.3 and Konclude
0.7.0 on generated nominal, rule, ALCHIQ, ALCI, merge, reflexive and
data-property inputs, including the fr282 dropped-rule miss, the
nominal-mode items deferred from v1.5.4 and nine bridge defects found after
the first candidate. It adds
exact native data-value reasoning (no answer depends on the 512-literal cap;
QUDT and the merge-and-count inputs are answered), a polarity encoding of
complement definers in the frontend, an exchange cut and composite Pred
premises in the nominal CB route, and an incremental form of the checked
subset blocking. Every calculus or encoding change is covered by a Lean
theorem or by a Lean checker whose acceptance implies exactness. The
acceptance contract is `docs/V1.5.5-ACCEPTANCE.md`; it has no amendment.
The campaign log with every branch and its measurements is
`docs/V1.5.5-STATUS.md`.

## Speed

The held-out half (585 ORE inputs) was run from the profile-guided binary
built from this tag (sha256 `5ac7eafe…`, the released executable) under the
v1.5.3 protocol (Ibex `batch`, `cpu_intel_gold_6248`, one core, 240 s,
20 GiB, scoped watchdog), on the same day (2026-11-09) and node pool as the
v1.5.3 release binary and as Konclude 0.7.0 (`Konclude-build-a`). Two
inputs that hit the cap on their first node were rerun once under the same
protocol and verified in 147 s and 166 s (`docs/V1.5.5-ACCEPTANCE.md`, S1).

| Clause | Status | Value |
|---|---|---|
| no loss | met | 577 verified against 558 (same-day v1.5.3) and 560 (v1.5.3 run of 2026-10-25); lost none; gained 17 against 2026-10-25 |
| mean ≤ 1.10 | met | 0.903 on the 558 inputs verified in both runs |
| median ≤ 1.10 | met | 0.827 |
| more verified than the same-day Konclude run | met | 577 against 575 (Konclude answered 578; three answers do not count) |
| mean and median against Konclude (reported) | KM slower | on 574 common inputs 3.94 s against 2.12 s, median 0.218 s against 0.202 s |

The seven held-out inputs KM does not verify besides the excused
`ore_ont_3794`: `ore_ont_10926` runs out of memory (Konclude answers it in
105 s); `ore_ont_2574` and `ore_ont_11196` time out (Konclude runs out of
memory); `ore_ont_8475`, `7192`, `15344` and `15695` time out for both.
Counted the same way, Konclude solved 576 held-out inputs on 2026-10-04;
the "558 against 554" of the v1.5.4 release note discarded 22 Konclude
answers whose comparison status was `inconsistent_agreement`
(`docs/V1.5.5-ACCEPTANCE.md`, "Finding on the Konclude count of record").
Against the first candidate, the bridge work of 2026-11-02 to 2026-11-09
brought the held-out mean from 0.944 to 0.903 and verified 15 more inputs.

The full regression pool (1,920 rows, 1,708 admitted) was run from the same
binary: 1,708 of 1,708 admitted inputs measured, 1,687 verified (v1.5.3 run
of 2026-10-25: 1,662; first candidate 1,671), lost none, gained 25
(`ore_ont_10838`, `11378`, `11647`, `12128`, `12191`, `15846`, `16315`,
`16420`, `16666`, `2792`, `3077`, `3087`, `3917`, `4567`, `4796`, `4903`,
`6132`, `699`, `7557`, `8148`, `8480`, `9151`, `9540`, `9577`, `9899`); no
wrong answer (`ore_ont_3794` is flagged and excused by the adjudication, as
in every run); 18 timeouts; `ore_ont_8250` refused with exit 3 (DL-safe
rules reach class queries through a nominal and the rule-worker input would
omit one SHIQ construct; v1.5.3 and v1.5.4 gave no answer on it either);
`ore_ont_4669` answered with no reference to compare against; the 212 rows
the manifest marks as invalid inputs were refused as required
(`pool-rc-55402594`; `ore_ont_10949` verified in 66 s on its protocol
recheck after a 240 s node timeout).

Full tables: `BENCHMARKS.md` among the release assets; records under
`/ibex/scratch/projects/c2014/hohndor/km/v155-release-20261109-rc3/`.

## Wrong answers fixed

The changelog lists every item with its branch. In summary:

- **Rules route.** Any consistent ontology with an executable DL-safe rule
  and an object nominal published the CB taxonomy without its rules and
  counted them as `DROPPED` (119 of 400 generated `fr` seeds in v1.5.4);
  binary object-atom rules beside a TBox nominal and a data property got no
  verdict. The rule worker now classifies its own input; 400 `fr` seeds with
  the Lean checker on: 380 ok, 0 wrong, 0 dropped, 20 timeouts.
- **Nominal CB route.** Side condition (*) blocked every r-Succ push of a
  query context whose element may be an individual (`r1600` missed `B ⊑ A`
  on the automatic route); the nominal-label cache read units off an ordered
  ground context; R3 did not deliver every clause inside the announced
  interface (four motifs, 480 of 2,000 and 155 of 1,000 motif seeds
  incomplete in v1.5.4). Fixed; `ExchangeEquality.lean` proves the
  propositional skeleton.
- **Ported Konclude bridge.** Three defects in the reuse of the consistency
  model and the forward role-assertion transfer with a target merged two or
  more hops away (2,000 merge seeds: 22 wrong to 0 on both routes; Konclude
  0.7.0 misses the same answers). After the first candidate, nine more
  (`docs/HYBRID-CB-HT.md` sections 18 to 25): the saturation refused `SELF`
  and published an incomplete taxonomy for ORE 12128; a role-successor count
  stub kept nominals from ever being merge-critical (m413); the at-least rule
  counted non-distinct successors and reported inconsistent
  reflexive-plus-functional inputs consistent; Konclude's NN rule was not
  ported (f1008, f439) and its per-candidate decisions did not terminate on
  seven seeds; the satisfiable-expander cache was misused on cached nodes
  next to nominals; two blocking tests of the optimized blocking accepted
  blocks Konclude refuses (sat578, both routes); and the existing-witness
  branch of the some-rule did not propagate the nominal-connection flag, so
  a probe root linked to a nominal entered the cross-probe cache as
  context-free. Every fix was checked against the Konclude source.
- **Nominal CB stack.** `x ≈ y` over Pred clauses and the root reach offers
  to the ground context (s974, s1966, nn1811), with the Lean enumeration
  and `root_label_hyp_sound` extended.
- **Global refutation stop.** Rows lost after the stop in the incremental CB
  oracle and the `km engine` worker; the automatic route missed the
  inconsistency of three ALCHIQ seeds.
- **Data values.** A value-singleton elision admitted a missing singleton
  before every value had a key; a finite range of more than eight values got
  no cover when the count bound was below two; the data-ABox omission
  accepted two values whose owners merge by inverse functionality; the
  bridge's satisfiable expander cache was reused beside consumed value
  singletons; `≥10 u.integer[1,9]` and `≥257 u.unsignedByte` were answered
  satisfiable.
- **Subset blocking.** The finite fold of the certificate copied only the
  blocker's successor edges; no wrong published answer was found (1,466 of
  1,500 ALCI seeds agree with HermiT), the fold now copies both directions
  and `check_sound` is proved for every choice of folds.

Differential coverage at the freeze: 4,000 random R3 seeds on the
automatic, `certified_nominals` and `nominals` routes; 1,000 seeds at 60 s;
2,000 merge seeds; 1,500 ALCI seeds; 400 `fr` rule seeds; 400 nominal-data
seeds; the data probes, fixtures and corner cases of `docs/DATATYPES.md`;
1,094 ORE design-half inputs with the frontend differential. No wrong answer
remains on any route. Timeouts are reported as timeouts and listed in
`docs/V1.5.5-STATUS.md`.

## Exactness

An input KM cannot answer exactly is refused with a reason or published with
the unrepresented axioms counted as `DROPPED`; it is never answered
approximately or with silently dropped axioms. Forced routes fail closed
without `KM_ALLOW_APPROXIMATE=1`. The data-range corners KM decides, drops
or refuses are listed in `docs/DATATYPES.md` ("Open corners"); dateTime
bound facets follow the XSD 1.1 order (timezoned and untimezoned values
compare only beyond fourteen hours), and non-canonical `rdf:XMLLiteral`
lexical forms are refused with exit 2.

## Lean boundary

The proved boundary is stated in
`docs/history/LEAN-BOUNDARY-AUDIT-2026-10-27.md`: a checker's acceptance of
an evidence document proves the answer exact for the normalised clauses in
that document; the frontend is unmodelled except for the passes named below;
procedure completeness is a theorem premise; no checker runs on the default
route unless `KM_LEAN_CHECKERS=<dir>` is set. New in 1.5.5, all without
`sorry` and depending only on propext, Classical.choice and Quot.sound:

- the rules route: `RulesRouteSemantics`, `RulesRouteRefutation`,
  `RulesRouteModel`, `RulesRouteCertificate` (executable `rules-cert-check`),
  `RulesInertSortRelease` (the inert object sort release, fifth gate
  `rules`);
- the hypertableau: `HypertableauSubsetUnravelling` (every mode 1/5 SAT
  terminal's unravelling checked as a finite model);
- the nominal CB route: `UniversalDefinerElimination`, `ExchangeCut`,
  `ExchangeEquality`, `CBPredResolving`, the `x ≈ y` case of
  `CBPredSendEnumeration` and the root reach offers (`root_label_hyp_sound`);
- the frontend: `PolarityDefiners` (`run_answers`), `ObjectGuardRestriction`,
  `DataAboxOmission`;
- data values: `TwoSortedDL`, `DataValueProjection`,
  `DataValueSingletonElision`, `DataRangeDateTime`.

The translation from the Rust clause structures to each Lean clause
language, the value-singleton inertness gate of the bridge and the rest of
the frontend are argued in the design documents, not mechanised; the
polarity pass is additionally checked by a 20,000-set differential unit test
against a literal transcription of the Lean definitions.

The checkers-on suite planned for v1.5.5 in `docs/CERTIFICATION-ROADMAP.md`
is in place (`docs/CHECKERS-ON.md`): 105 checkers inventoried,
`KM_LEAN_CHECKERS=<dir>` runs every applicable one on the classification
route and exits 6 with no answer on any rejection; 1,781 inputs ran with the
checkers on (0 answer changes, 0 wrong against HermiT), and the certificate
defects the suite found are fixed. All five production Lean certification
gates (`elc`, `routing`, `ht`, `cb`, `rules`) were executed from the exact
tagged commit with zero `sorryAx`, alongside the serial Rust CI suite (the
22 checker-bound tests run inside the gates and in the checker step), the
checker step with the released binary, and the Maven Java suite. The gate
receipts, test logs and tool bindings are in `build-completion.json` among
the release assets.

Gate times from the tag on 2026-11-09: `elc` 47 s on the cached build,
`routing` 10 min, `ht` 49 min, `cb` 7 min, `rules` 9 min; zero `sorryAx`
everywhere. The checker step with the released binary: 57 checker-bound
test groups passed, checkers-on suite 22 and 33 accepted, 0 rejected, 0
answers changed in modes `on` and `ht` (`docs/CHECKERS-ON.md`, section 6).

## Reproducing and inspecting the release

Build the tagged source with `cargo build --locked --release --features
mimalloc --bin km` in `engine/` (with `RUSTFLAGS="-Cprofile-use=merged.profdata
-Cllvm-args=-pgo-warn-missing-function"` for the profile-guided build;
pipeline receipts under the release assets). Reproduce the JAR with
`mvn package` in `protege/`. The release procedure as executed is
`docs/RELEASE-1.5.5-PROCEDURE.md`.

The release attaches:
- `km-v1.5.5-linux-x86_64`: the measured native executable.
- `kobayashi-marust-protege-1.5.5.jar`: the Protégé / OWLAPI package.
- `km-v1.5.5-certified-source.tar.gz`: the exact final source archive.
- `BENCHMARKS.md`: held-out and pool tables and the G8 comparison.
- `build-completion.json`: machine-readable results and certification bindings.
- `SHA256SUMS`: checksums of the other five files.
