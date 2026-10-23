# KM 1.5.2 release and benchmark protocol

Version 1.5.2 extends source-level incremental reuse, eliminates all `full_classify`
update fallbacks across the 80-ontology incremental benchmark, and improves both
retained-session initialization and fresh classification on large flat taxonomies
and OWLAPI sessions. It removes the v1.5.1 whole-session performance exception
(`docs/release-1.5.1-performance-exception.json`): every evaluated update cell and
every completed whole session on both CLI and OWLAPI improves over classification
from scratch. The [incremental reasoning guide](INCREMENTAL-REASONING.md) documents
the request/response protocol, rollback guarantees, reuse receipts, and safety gates.

## Exact implementations and competing method identities

| Method / benchmark arm | Version | Source commit / coordinate | Artifact SHA-256 | Execution / scope |
|---|---|---|---|---|
| Candidate native, retained and fresh | KM 1.5.2 | `1f4fb91e61ae072aa64ad6d8ca58732a77e90a59` | `5bdced8e7926686927799b61549cdc19e122487d36d32f58d48a25d064c0662b` | Release, mimalloc, no PGO; 1,920-ontology static classifier (`km classify`), persistent source session (`candidate_retained`), and fresh per-revision classifier (`candidate_fresh`) |
| Candidate OWLAPI adapter | KM 1.5.2 | `1f4fb91e61ae072aa64ad6d8ca58732a77e90a59` | `25f9f66f7f7164225f65cfc04ab8c335b3f25f394a9153a45dec942370cc0053` (JAR), `19f6903a6b680ff5bb1b4bbd038b2c3c02ea94797f92b48ce3baffecb7523e33` (compile receipt) | Maven, JDK 17.0.20.1+1; retained and fresh OWLAPI sessions |
| Released baseline, retained and fresh | KM 1.5.0 | `d95f0b840a433b5b43c4eff48092e8b600bca8de` | `1dbc0dd92170abcd70e948fa2dc2d9d13d5c72076bcff9ad7a664921188e5900` | Published profile-use executable and v1.5.0 Java adapter (`released_baseline_retained` and `released_baseline_fresh`) |
| Prior incremental release reference | KM 1.5.1 | `2823c0ebd98ec9d6f4afd2cdb19bb0ba5bffab2a` (native `4dd7995b5def62bb8f9140dd2be62b671816f71b`, adapter `11db48ce73029227c7a28b9ad5e2e2a25189cc2a`) | `5ee715d66e391e561e188c735a8fa6a0aaabc4383e7d8bd243b52495b2cac3a8` (native), `8ffdfbc4d3e947afe1b03d86a17bb9d57ff5f73b12acfc01b1f2d00f5e2cabb9` (JAR) | Prior incremental release benchmarked under the same 80-ontology input plan |
| Konclude | `v0.7.0-1138` | `0002e80635403960a7df5d93bd0e8f994d4952d0` (embedded banner `500e11d9`) | `e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4` | 1,920-ontology correctness reference and comparative baseline |
| RustDL (updated latest) | `v0.4.41` | `7bf5af7e1b1381bf879540f433d6b5f0f4c70f89` (tag `v0.4.41`: `6f50561fdf5ed6b442cd9e3da38a05c78c076645`) | `52f3e03be74a82a51854e76e26cc4aa95681f87f340f1ba11fa81fecffc243a1` | 1,920-ontology comparative benchmark (updated latest) |
| RustDL (v1.5.0 baseline) | `v0.4.28` | `b120b1783dc83838df186591b18ac68891a2e87d` | `20b31b3f53474e95e533e0eae84d7d85da48be6987599f4ba6ee947e65ab6bea` | 1,920-ontology comparative benchmark (historical baseline) |
| ELK | `v0.6.0` | `b8ac5ce83db0704a7359d96aa382891e2f547863` | `7ffc442f2966667a488479a748502276136445c8e44ffd9e8498873a401cb3d4` | 1,920-ontology and ORE 2015 comparative baseline |
| HermiT | `1.4.5.519` (`1.4.6.519-SNAPSHOT` in ORE table) | Maven `net.sourceforge.owlapi:org.semanticweb.hermit:1.4.5.519` | `59a7dc34d874c0dd9fb752594eb8d55b611e70d3cf7e839d581d7c366a5dd99c` | 1,920-ontology correctness reference and ORE 2015 comparative baseline |
| Openllet | `2.6.5` | Maven `com.github.galigator.openllet:openllet-owlapi:2.6.5` | `43671b4a4ea06a24834183b5c55cdb3830fe1c96d33ffe56b32a5167d6f0319f` | 1,920-ontology correctness reference |
| JFact | `5.0.3` | Maven `net.sourceforge.owlapi:jfact:5.0.3` | `06f85fd8e6cc647f7436b8a13da13a4d0b03b2df1d1184394ebe885f29c65867` | 1,920-ontology correctness reference |
| Whelk | `v1.2.1` | `cd559645c89337190331e66673dc6d31eed5a291` (tag `d0f430f6468b6449cbaa6cf3e5d63f4042aae998`) | `e5ce43b18ee9e8ada9ce9cc2a7cea35f6658d56089b3d4caa4bb9bfec2fce55b` | Comparative benchmark baseline |
| MORe | `0.2.0-SNAPSHOT` | `9d29fb15352b781a3dba015696b1b269320603b2` | `1097e637fd25f2f64b9fd63c1f0f2ab24c2c2c3a198b7b5c521ea43915840302` | Comparative benchmark baseline |
| Sequoia | `0.6.1-alpha` | `c5248ec7be30` | `a84dfc7b30cb46dfd9333ef89ac6c2b1cd3bb27025777cc02f8c84b6df7a7649` (launcher), `283a6b1b0f1113a4c40403f81eab28bc972926cd984f9e484a949ffbfbd6f39f` (runtime manifest) | Comparative benchmark baseline |

The final release commit adds release documentation; its `engine/`, `lean/`, and
`protege/` trees match commit `1f4fb91e61ae072aa64ad6d8ca58732a77e90a59` with an
empty tree diff. The annotated `v1.5.2` tag, `BENCHMARKS.md`, and
`build-completion.json` identify the exact final release commit. No abbreviated
commit serves as a source binding.

## 1,920-ontology total static classification benchmark

The total static classification benchmark evaluates `km classify` across the
frozen 1,920-ontology corpus (`full-candidate-inputs.json`, SHA-256
`0309377d05dfd0cd81eb46050416272fbd52b16e77f21d9a37d732b352817fb4`), comprising
`1,708` admitted `checks_passed` ontologies and `212` `invalid_input` expected
refusals under a 240-second timeout, 20,480 MiB process-tree RSS limit, and
single-core execution (`KM_THREADS=1`, `RAYON_NUM_THREADS=1`, `OMP_NUM_THREADS=1`).

KM 1.5.2 (`5bdced8e7926686927799b61549cdc19e122487d36d32f58d48a25d064c0662b`) solves
`1,660 / 1,708` admitted ontologies verified against the four independent
correctness reference reasoners (`konclude`, `hermit`, `openllet`, `jfact`),
refuses `212 / 212` invalid inputs with exit code 2 (`0` unresolved), and produces
`0` taxonomy differences across all `1,660` completed classifications compared
against released KM 1.5.0 (`1dbc0dd92170abcd70e948fa2dc2d9d13d5c72076bcff9ad7a664921188e5900`).
Updated `RustDL v0.4.41` (`7bf5af7e1b1381bf879540f433d6b5f0f4c70f89`, SHA-256
`52f3e03be74a82a51854e76e26cc4aa95681f87f340f1ba11fa81fecffc243a1`) was also built
and evaluated under the same 1,920-ontology harness, increasing RustDL's verified
completions from `1,212` (`v0.4.28`) to `1,428` (`v0.4.41`, `+216` solved).

| Method | Version / commit | Verified solved / 1,708 | All-verified mean / median (s) | Common verified with KM 1.5.2 | KM 1.5.2 common mean / median (s) | Competitor common mean / median (s) | KM 1.5.2 gained / lost |
|---|---|---:|---:|---:|---:|---:|---:|
| KM 1.5.2 (candidate) | `v1.5.2` / `1f4fb91e61ae` | 1,660 | 5.6605 / 0.3209 | 1,660 | 5.6605 / 0.3209 | 5.6605 / 0.3209 | 0 / 0 |
| KM 1.5.0 (released baseline) | `v1.5.0` / `d95f0b840a43` | 1,661 | 3.2557 / 0.2305 | 1,660 | 5.6605 / 0.3209 | 3.1854 / 0.2305 | 0 / 1 |
| Konclude | `v0.7.0-1138` / `0002e8063540` | 1,655 | 2.9232 / 0.2690 | 1,641 | 4.6074 / 0.3137 | 2.9347 / 0.2668 | 19 / 14 |
| RustDL (updated latest) | `v0.4.41` / `7bf5af7e1b13` | 1,428 | 8.5060 / 0.6576 | 1,419 | 2.3638 / 0.2462 | 8.3728 / 0.6257 | 241 / 9 |
| RustDL (v1.5.0 baseline) | `v0.4.28` / `b120b1783dc8` | 1,212 | 5.1386 / 0.3312 | 1,205 | 2.2889 / 0.2407 | 5.0630 / 0.3183 | 455 / 7 |
| ELK | `v0.6.0` / `b8ac5ce83db0` | 1,411 | 11.9712 / 4.7772 | 1,399 | 3.4796 / 0.2479 | 11.7327 / 4.7464 | 261 / 12 |

## Defensible incremental reasoning benchmark protocol

### Corpus and revision structure

The benchmark uses the frozen 80-ontology selection from the ORE 2015 pool
(selection SHA-256 `d51dff7640b82a84ccf22857532817c39c1952c9b6c7e2acd00ad4df6ab246e7`).
Each ontology has nine deterministic source revisions (`r0..r8`):
- `r0`: initial complete ontology snapshot (`init`).
- `r1..r6`: single-axiom and multi-axiom TBox additions, removals, and restorative
  edits testing module reuse, exact taxonomy reuse, and inconsistency-witness reuse.
- `r7..r8`: broader TBox, RBox, nominal, or ABox updates testing common-module,
  common-object-module, positive-ABox-module, and nominal-subject reuse.

Across 80 ontologies, each path (`cli` and `owlapi`) schedules 80 whole-session
sequences (`r0..r8`, 720 revisions) and 640 incremental update cells (`r1..r8`).

### Four-arm counterbalanced design

Every ontology and path is evaluated across four arms:
1. `candidate_retained`: KM 1.5.2 persistent session (`km incremental-source` on CLI;
   retained `KMReasoner` with `BUFFERING` flush on OWLAPI).
2. `candidate_fresh`: KM 1.5.2 fresh classification from scratch on each revision
   (`km classify` on CLI; fresh `KMReasoner` per revision on OWLAPI).
3. `released_baseline_retained`: KM 1.5.0 persistent session.
4. `released_baseline_fresh`: KM 1.5.0 fresh classification from scratch on each revision.

Each ontology runs for five paired repetitions (`repetition 0..4`). Arm execution
order is counterbalanced across repetitions using a Latin square so cache warmth
and system noise do not systematically favour any arm.

### Resource isolation and cleanup verification

Each worker runs pinned to a single physical CPU core (`KM_THREADS=1`,
`RAYON_NUM_THREADS=1`, `OMP_NUM_THREADS=1`, `-XX:ActiveProcessorCount=1`), with a
240-second per-request wall-clock limit and a 20,480 MiB process-tree RSS limit
enforced by a dedicated watchdog. Every invocation runs inside a Linux
`PR_SET_CHILD_SUBREAPER` scope that verifies zero surviving descendant processes
before and after each arm (`cleanup_proven_empty: true`).

### Acceptance metrics and denominators

For each update cell (`r1..r8`), acceptance uses the median of the five paired
`candidate_retained / candidate_fresh` ratios (not the ratio of unrelated aggregate
medians). Every evaluated update cell must have a median paired ratio strictly below
`1.0`. Whole-session comparisons include initialization (`r0..r8`) and require the
five-repetition `candidate_retained` session median to be strictly below the
`candidate_fresh` session median (and below `released_baseline_fresh` wherever the
baseline completes):
- **CLI update metric**: end-to-end request/update wall time.
- **CLI whole-session metric**: driver-observed session wall time including
  process spawn, `r0` initialization, `r1..r8` updates, and shutdown.
- **OWLAPI update acceptance metric**: reasoner work
  (`apply_flush_ns + taxonomy_publish_and_cleanup_ns`).
- **OWLAPI additional reporting**: harness OWL parsing time (`parse_ns`) and
  end-to-end wall time, plus whole-session wall time including `r0` initialization.

All 80 cases and 640 update cells per path remain in the denominator. On
`ore_ont_16744`, KM 1.5.2 (`candidate_retained` and `candidate_fresh`) completes
all nine revisions across all five repetitions on both CLI and OWLAPI, whereas
KM 1.5.0 times out on updates 7 and 8 on CLI and at initialization on OWLAPI; on
OWLAPI, KM 1.5.0 also has baseline non-completions on `ore_ont_10689` and
`ore_ont_15703`, while KM 1.5.2 completes all five repetitions of both. Both the
79-case candidate-complete denominator (`632 / 640` update cells on CLI and OWLAPI)
and the four-arm-complete denominator (`78 / 80` cases and `624 / 640` cells on CLI;
`76 / 80` cases and `608 / 640` cells on OWLAPI) are reported. Only `ore_ont_1194`
times out at 240 seconds across all four arms.

| Path | Candidate-complete cases / 80 | Four-arm-complete cases / 80 | Evaluated update cells / 640 | Cells below 1.0 | Whole sessions faster than candidate fresh | Whole sessions faster than both fresh arms (4-arm) |
|---|---:|---:|---:|---:|---:|---:|
| cli | 79 | 78 | 632 (624 4-arm) | 632 (624 4-arm) | 79 / 79 | 78 / 78 |
| owlapi | 79 | 76 | 632 (608 4-arm) | 632 (608 4-arm) | 79 / 79 | 76 / 76 |

Every evaluated update cell (`632 / 632` CLI and `632 / 632` OWLAPI) has median
paired ratio `< 1.0`, every completed whole session (`79 / 79` CLI and `79 / 79`
OWLAPI) beats `candidate_fresh` and every available fresh baseline, zero
`full_classify` update fallbacks occur on any completed update (`r1..r8`), and zero
semantic differences occur across arms.

## Key technical changes in v1.5.2

1. **Direct `flat_nf1` classification for unary-subsumption ontologies**:
   `engine/src/orchestrate/flat_nf1.rs`, `engine/src/routing.rs`,
   `engine/src/source_locality.rs`, and `engine/src/named_subclass_validation.rs`
   detect assertion-free ontologies whose TBox consists solely of named unary
   `SubClassOf(A, B)` axioms, declaration axioms, and annotations, and compute the
   exact transitive named-class closure directly over dense integer IDs while
   producing the same certified ELC publication evidence and incremental locality
   state. This recovers `ore_ont_16744` updates 7 and 8 from 240-second timeouts
   down to ~0.4–13 seconds.
2. **Exact cross-revision compiler donor and localized support reuse**:
   `engine/src/incr_session.rs` upgrades assertion-free initial TBox indexes to
   `exact_full` compiler donors and extends localized incremental reuse in
   `engine/src/incr_support/rules.rs` and `engine/src/incr_support/object.rs`,
   eliminating all remaining `full_classify` update fallbacks across `r1..r8`.
3. **OWLAPI retained initialization and compact wire transport**:
   `protege/src/main/java/org/bioontology/kobayashimarust/protege/KMReasoner.java`,
   `Classifier.java`, and `RetainedFunctionalSyntax.java` initialize retained
   OWLAPI sessions directly via `sendSessionInit` (avoiding a duplicate upfront
   one-shot `km classify` subprocess) and stream compact functional syntax without
   non-semantic comment lines or per-token flushes. On `ore_ont_2713` (the v1.5.1
   whole-session exception), retained OWLAPI whole-session time is now faster than
   both fresh arms.

## Correctness and certification

For each measured revision, canonical taxonomy hashes and consistency are checked
across all completed arms (`0` differences across all 7,020+ available arm checks).
All four production Lean certification gates (`elc`, `routing`, `ht`, `cb`) are
executed from the exact tagged release commit with zero `sorryAx`, alongside the
full 45-command serial Rust CI test suite and the 76-test Maven Java suite.

## Reproducing and inspecting the release

Build the tagged source using `cargo build --locked --release --features mimalloc
--bin km` in `engine/`. Reproduce the JAR with `mvn package` in `protege/`.

The release attaches:
- `km-v1.5.2-linux-x86_64`: the measured native executable.
- `kobayashi-marust-protege-1.5.2.jar`: the measured Protégé / OWLAPI package.
- `km-v1.5.2-certified-source.tar.gz`: the exact final source archive.
- `BENCHMARKS.md`: final results, including per-case and per-update tables.
- `build-completion.json`: machine-readable results and certification bindings.
- `SHA256SUMS`: checksums of the other five files.

Download all files into one directory and run `sha256sum -c SHA256SUMS`. The
annotated `v1.5.2` tag binds the manifest by its HTTPS location and SHA-256.
