# Checkers-on suite (v1.5.5, 2026-10-30)

Agent `checkers-on-suite`, branch `fix/v155-checkers-on-suite` off
`development/v1.5.5` (87fda54f). Design and inventory: `docs/CHECKERS-ON.md`.

## What was measured

`km classify --lines` on 1,781 inputs, each in three modes, on the
workstation (four runs at a time, `KM_THREADS=1`, 60 s per run, every other
`KM_*` variable removed):

| mode | setting |
|---|---|
| `off` | no checker |
| `on` | `KM_LEAN_CHECKERS=<dir>`: ELC publication checker and the two CB taxonomy publication checkers; HT workers unchecked |
| `ht` | `on` plus `KM_LEAN_CHECKERS_HT=1` (certified HT workers) |

Per input and mode: route (`KM_TIMING` frontend line), exit status, answer
digest (consistency, subsumptions and unsatisfiable classes; every
inconsistent answer has the same digest), HermiT verdict where a cached
answer exists, every `KM_LEAN_CHECK` event, wall time.

An `on` or `ht` run is counted as

* **accepted** when a publication-level certificate (ELC publication, CB
  source-exact or source-production taxonomy, HT taxonomy or verdict) was
  accepted and nothing was rejected. This says a checked worker's answer is
  exact for the clause set in its certificate. It does not say that this
  worker's answer is the one the supervisor published; the suite verifies
  separately that the published answer equals the unchecked run's answer;
* **rejected** when any checker rejected any certificate (the run then
  publishes nothing, exit 6);
* **cannot_check** when the run published an answer but no publication-level
  certificate was accepted (the reasons are listed per event);
* **no_answer** when the run published nothing for another reason (timeout,
  or the unchecked run also had no answer).

## Inputs

| family | count | source |
|---|---:|---|
| fixture | 186 | every `.ofn`/`.owl`/`.ttl` under `engine/tests/fixtures/` |
| nominal | 100 | every 4th of `gen_nomdata.py --no-inverse` seeds 2000-2399 (`.work/agent-scratch/per-context-order/fresh2`, HermiT gold `gold_fresh2`) |
| data | 100 | every 2nd of seeds 7000-7199 (`.work/agent-scratch/top-nominal-data/fresh3`, gold `gold_fresh3`) |
| rule | 100 | every 4th of `gen_finite_rules.py` seeds (`.work/agent-scratch/rules-worker-cost/seeds2/ofn`, gold `seeds2/gold`) |
| bridge | 100 | every 4th of the ALCHIQ seeds g301-g700 (`.work/agent-assets/2026-10-28-scratch/bridge/seeds`, gold `bridge/gold`) |
| cardinality | 101 | every 3rd of the ALCHIQ seeds g1-g300 (`.work/agent-assets/2026-10-28-scratch/sq`, gold `bridge/gold`) |
| ore | 1,094 | design half of `results/benchmarks/2026-10-26-v154-routing/split.json` whose v1.5.3 run (`.work/v153-correctness-1920`) finished within 60 s; files `v150-corpus/files/` (all 1,094 SHA-256 equal to the v1.5.3 records) |

The lists are `inputs/*.tsv` (absolute paths on the workstation).

## Binaries

* `km`: built from the engine sources of 59306389 before `rustfmt` reflowed
  `engine/src/lean_checkers.rs` (whitespace only; 108ba366 renames a unit
  test), `cargo build --release`, SHA-256
  `45df9286cd71b2777643ab176357f3801dc42676950f4ba8fb3df1d10f42c793`.
* Lean checkers: the 105 executables of `lean/lakefile.toml` built from the
  Lean sources of v1.5.4 (identical to `development/v1.5.5`; the 105 lake
  trace hashes equal those of the v1.5.4 gate build
  `.work/gates-4dd7995b`). SHA-256 of every executable: `binaries.sha256`.

## Reproduce

```bash
tools/checkers-on-suite.sh KM lean/.lake/build/bin OUT inputs/fixtures.tsv inputs/seeds.tsv inputs/ore.tsv
# SUITE_GOLD=dir1:dir2:... adds HermiT answer directories
```

`summary.md` and `per-input.tsv` are written by
`python3 -I tools/checkers_on_suite.py summarize OUT`; `results.jsonl.gz` is
the raw record.

## Results

See `summary.md` (generated) and the sections below.

### Totals (1,781 inputs; `summary.md` has the per-family, per-route and per-checker tables)

| mode | accepted | rejected | cannot_check | over_budget | no_answer | answers changed | wall ratio vs off |
|---|---:|---:|---:|---:|---:|---:|---|
| `on` | 34 | 231 | 1,014 | 380 | 122 | 0 | 1.16 (1,045 inputs both answer) |
| `ht` | 34 | 365 | 662 | 595 | 125 | 0 | 1.81 (696 inputs both answer) |

The unchecked run answered 1,657 inputs (124 time out or fail without
checkers too). Every cached HermiT answer agrees with every published
answer in every mode (off 491 ok, on 476 ok, ht 306 ok, no WRONG).

* All 34 accepted runs are ELC publication certificates (28 ORE, 6
  fixtures), all on existential-free inputs. No CB certificate was accepted
  in a run without a rejection in `on` mode; in `ht` mode, where most HT
  workers decline and the CB worker answers, the CB checkers accepted 88
  certificates and rejected 78.
* No HT certificate was produced on the automatic route, also with
  `KM_LEAN_CHECKERS_HT=1`: the bridge's compact output cannot bypass HT
  certification (1,160 events), certified HT requires the global consistency
  route (90), or the input has no certified HT route (5).
* CB `cannot_check`: nominal mode (199 events in `on`; certified CB would
  run the incomplete unordered regime), typed source declined (18), no
  standalone production derivation (6), no blocked saturation (6).
* `over_budget`: 380 inputs (379 ORE) answered within 60 s without checkers
  but not with them. These are ELC certificates of 1 MB to 90 MB; the ELC
  checker took 125 s on the 87 MB certificate of `ore_ont_10254` (0.9 MB
  ontology) and rejected it.

### Rejections

No rejection hides a wrong answer: each minimised case below agrees with
HermiT, and every rejected input's unchecked answer that has a cached
HermiT answer agrees with it. Every rejection is a certificate the checker
cannot accept for a correct answer, that is, a defect in the producer or in
the checker's wire contract. Inputs: `per-input.tsv`, column `reason_on`/`reason_ht`.

| id | checker | message | inputs (on / ht) | minimal input | cause |
|---|---|---|---|---|---|
| E1 | `elc-cert-check` | trace is unsound or materialization is not closed | 231 / 365 (all ELC rejections; one message for both causes) | `minimal/elc-skolem-pair.ofn` (`D ⊑ ∃r.A`) | `checkNormalizationV5` fails: `certifyRawDirectToNormal` (`ELRawNormalization.lean:1059`) accepts no Skolem half, and the Rust producer emits witness records only when a residual is compiled (`elcomplete.rs` `build_lean_source_partition`, `residual_skolem_witnesses` empty when `residual.is_empty()`). So every certificate with an existential restriction is rejected. 11 of 12 sampled ORE rejections have Skolem halves and no witness record; all 28 accepted ORE certificates have none. |
| E2 | `elc-cert-check` | same message | 1 of the 12 sampled ORE rejections (`ore_ont_7482`) | `minimal/elc-disjointness-bottom.ofn` (`C ⊑ A`, `DisjointClasses(A B)`), rejected on `production_all`, accepted on `elc` | `checkSignatureClosed` fails: the `production_all` EL arm normalises the disjointness to `nf2 A B ⊥`; `Clause.concepts` (`ELCompletionWire.lean:436`) includes ⊥, `checkSignatureClosed` requires every clause concept to be active, and `checkActiveConcepts` requires the active set to exclude ⊥ (`expectedActiveConcepts`, line 446). No certificate with a ⊥ head in `nf1`/`nf2`/`nf4` can pass. |
| C1 | `cb-source-production-taxonomy-check` (and `cb-source-taxonomy-cert-check` on a forced CB route) | decoded CB ontology differs from the allocated verified source encoding | 3 / 22 (all contain `FunctionalObjectProperty`) | `minimal/cb-functional-source-encoding.ofn` (`FunctionalObjectProperty(:s)` alone) | The typed-source compiler accepts the functional property, but the certificate's decoded ontology differs from the checker's own encoding of the typed source. `docs/CB-CERTIFICATION.md` lists functionality as outside the evidence form; the producer should decline (cannot check) instead of emitting a mismatched document. |
| C2 | `cb-source-production-taxonomy-check` | standalone CB local trace omits its claimed result | 0 / 3 | `minimal/cb-production-standalone-trace.ofn` (`(C⊔D)⊓(C⊔A) ⊑ C`, `D ⊑ A`, `Q3 ≡ D⊔C`; forced `cb_plain1`) | The source-exact checker accepts the same run; the standalone context proof for one cell does not end in the clause it claims. |
| C3 | `cb-source-production-taxonomy-check` | `WireDocument.proof … WireProductionEntry.justification: object expected` | 0 / 1 | `minimal/cb-production-justification-decode.ofn` (`D ⊑ ∃t.∀s.C`, `⊤ ⊑ ¬D`; automatic route with `KM_LEAN_CHECKERS_HT=1`) | The production trace carries a justification that is not a JSON object, so the document does not decode (wire drift between the Rust writer and `CBProductionTraceWire`). The forced `cb_plain1` run of the same input is accepted. |

Found outside the suite (with the real checkers supplied to tests the gates
run with stubs):

| id | checker | message | where |
|---|---|---|---|
| H1 | `ht-cert-check` | `WireCertificate.node_count: Natural number expected`, then `identity-normalized global decision has no ontology` | `tests/ht_taxonomy_certificate.rs` `accepted_complete_taxonomy_is_the_published_classification` with `KM_HT_TEST_LEAN_GLOBAL_CHECKER=ht-cert-check` (the test defaults to `/bin/true`, and no gate exports the variable); also `km classify --route ht_general` with the HT checkers and `KM_HT_GLOBAL=1` |
| B1 | `cb-live-taxonomy-publication-check` | `…global_model…global_closure.version: Natural number expected` | the bundle at `KM_CB_CERT_BUNDLE` embeds the typed source as `global_model`, which the live publication wire decodes as a global-model document; the bundle of both inputs in `component/` is rejected (component set `all`) |
| B2 | the eight `cb-source-*-closure` and live-insertion checkers | source-bound CB context still has dirty r-Succ edges | `component/d-some-r-a.ofn` (`D ⊑ ∃r.A`), while both taxonomy publication checkers accept the same run; all accept `component/a-sub-b.ofn` (`component/cb-component-checkers.txt`) |
| T1 | (test expectation) | `lean_taxonomy_checker_accepts_a_materialized_equality_body` asserts `payload.plain.certificate`, absent from the current wire | runs only when `KM_HT_TEST_LEAN_TAXONOMY_CHECKER` is set, which no gate does |

A run of the fixtures with `KM_LEAN_CHECKERS_SET=all` (`run-all-fixtures`,
not kept) produced no CB component event: on the automatic route no CB worker
reached certification on a fixture (the race answered first, or the input
was in nominal mode or outside the typed source).

### Tests

| suite | result |
|---|---|
| the 22 lib tests of the CI skip list (`.github/workflows/ci.yml`), one at a time, with `lean/checker-env.sh` | 22 passed (`tests/lib-ci-skip-list-with-checkers.log`) |
| whole lib suite, checker env, 4 threads | 2,999 passed, 30 failed, 10 ignored; 22 of the 30 pass when rerun one at a time (Lean checkers fail to start threads under the host's commit limit when run in parallel); the other 8 are production-path tests that fail under the full checker env and pass without it (two of them: `regular_certificate_serializes_general_guarded_residual_bodies` needs `CARGO_TARGET_DIR`, set by the recipe; T1 above) |
| whole lib suite, no checker env, 4 threads | 3,008 passed, 21 failed (exactly the skip list that does not skip on its own), 10 ignored; no `orchestrate::` failure |
| every integration target, no checker env, 2 threads | 336 passed, 5 failed, 1 ignored; the 5 (`certified_abox_production` 1, `finite_data_rule_normalization` 3, `has_key_rules` 1) assert which route answered and pass when rerun with one thread |
| `cb_live_state`, `elc_certificate` with checker env | 12/12, 3/3 |
| `ht_taxonomy_certificate` | 16/16 without env; with the gate env 2 to 4 fail (H1, and thread start failures) |
| `lean_checkers_dir` (new) | 5/5 with stubs only, 5/5 with `KM_TEST_LEAN_CHECKERS_DIR` (real ELC and CB checkers reject the corrupted certificates and `km classify` exits 6 with no output) |
| `lean_checkers::tests` (new) | 3/3 |
| `data_assertions_carried` (bound fix) | 9/9; `unproxied_assertions_can_hide_a_clash` 136 s under the suite's load, within the new 240 s guard |
