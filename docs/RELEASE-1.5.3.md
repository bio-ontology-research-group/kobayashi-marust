# KM 1.5.3 release and benchmark protocol

Version 1.5.3 resolves the static-classification performance and coverage
discrepancy observed in v1.5.2 on the 1,920-ontology corpus, adds engine and
routing optimizations that recover both `ore_ont_2874` and `ore_ont_8509`
(`1,662 / 1,708` verified solved, up from `1,660` in v1.5.2 and `1,661` in
v1.5.0), and beats Konclude (`v0.7.0-1138`), KM 1.5.0, KM 1.5.2, RustDL
(`v0.4.41` and `v0.4.28`), and ELK (`v0.6.0`) in both mean and median
classification time under matched hardware, single-core execution, and build
conditions. Across the 80-ontology four-arm incremental benchmark, every
evaluated update cell (`632 / 632` CLI and `632 / 632` OWLAPI) and every
completed whole session (`79 / 79` CLI and `79 / 79` OWLAPI) improves over
classification from scratch with zero semantic differences. The
[incremental reasoning guide](INCREMENTAL-REASONING.md) documents the
request/response protocol, rollback guarantees, reuse receipts, and safety
gates.

## Root-cause diagnosis of the v1.5.2 classification discrepancy

Audit of the v1.5.2 1,920-ontology run (`5.6605 s` mean, `0.3209 s` median,
`1,660` verified solved) against KM 1.5.0 (`3.2557 s` mean, `0.2305 s` median,
`1,661` verified solved) and Konclude (`2.9232 s` mean, `0.2690 s` median,
`1,655` verified solved) identified three evaluation-environment mismatches and
several engine hotspots:

1. **Unscoped `/proc` watchdog CPU starvation and post-exit sleep latency**:
   In the 1,920-ontology harness, `tree_watchdog.snapshot_all()` scanned every
   PID in `/proc` across the entire host at 50 Hz (`20 ms` interval) while
   pinned to the same single CPU core as the `km` worker. On a multi-worker
   host, scanning all host processes consumed up to 58% of the single pinned
   core and added up to `20 ms` of post-exit polling latency on every short
   ontology. Replacing global `/proc` enumeration with scoped descendant
   tracking (`ScopedSnapshot`, reading only `/proc/<pid>/task/<tid>/children`
   and the process cgroup's `cgroup.procs`, `max_scope_pids: 3..5`) and kernel
   `pidfd` exit readiness (`start_exit_observer`) reduces watchdog CPU overhead
   to 1.6% and eliminates post-exit sleep latency while preserving process-tree
   RSS accounting and subreaper cleanup verification.
2. **Hardware and multi-worker contention mismatch**:
   KM 1.5.0, Konclude, ELK, and RustDL `v0.4.28` were measured on IBEX
   `cpu_intel_gold_6248` nodes (Intel Xeon Gold 6248 @ 2.50 GHz, Cascade Lake),
   whereas KM 1.5.2 was measured on a local Broadwell workstation (Intel Xeon
   E5-2680 v4 @ 2.40 GHz) with 20 concurrent workers sharing socket memory
   bandwidth. Running KM 1.5.3 on the matched IBEX `cpu_intel_gold_6248`
   hardware removes the cross-architecture and memory-bus penalty.
3. **Profile-guided optimization (PGO) build parity**:
   KM 1.5.0 (`1dbc0dd92170abcd70e948fa2dc2d9d13d5c72076bcff9ad7a664921188e5900`)
   was compiled with LLVM profile-guided optimization (`-Cprofile-use`,
   `lto = true`, `codegen-units = 1`, `--features mimalloc`), whereas KM 1.5.2
   (`5bdced8e7926686927799b61549cdc19e122487d36d32f58d48a25d064c0662b`) was
   compiled without PGO (`15–25%` slower on tight saturation and completion
   loops, causing borderline `ore_ont_2874` to cross the 240-second cutoff).
   KM 1.5.3 restores PGO (`profile_sha256`:
   `63c8227e30b6008625bacce2e2ff2e6986a1c124e7bba702f993e4b9019f745b`).
4. **Engine, frontend, and routing optimizations in v1.5.3**:
   Copy-on-write node resolution vector storage (`engine/src/tableau.rs`),
   single-word clause head bitsets (`engine/src/clause.rs`), fast integral
   decimal screening (`engine/src/frontend/conformance.rs`), compact EL-ABox
   fallback retry without disk reload (`engine/src/orchestrate/runner.rs`),
   classifier-owned atomic ABox projection across the screened nominal-free
   object fragment and anonymous individuals (`engine/src/abox_project.rs`),
   and refined HT bridge-first and certified-nominal routing guards
   (`engine/src/routing.rs`) solve `ore_ont_8509` in `4.02 s` (a 240-second
   timeout in both v1.5.0 and v1.5.2) and cut ~600 seconds of cumulative wall
   time across heavy ontologies (`ore_ont_11085`, `ore_ont_7203`,
   `ore_ont_4609`, `ore_ont_12698`, `ore_ont_13690`, `ore_ont_7007`,
   `ore_ont_9053`, and `ore_ont_16056`).

## Exact implementations and competing method identities

| Method / benchmark arm | Version | Source commit / coordinate | Artifact SHA-256 | Execution / scope |
|---|---|---|---|---|
| Candidate native, retained and fresh | KM 1.5.3 | `ecc4b1c57bc799bd8b2cf501fb5c2921607d9051` | `2470b0415f1a78533024e15b5c317f9e743a98916b597739db93b9452a8dd8d4` | Release, mimalloc, PGO (`63c8227e…19f745b`); 1,920-ontology static classifier (`km classify`), persistent source session (`candidate_retained`), and fresh per-revision classifier (`candidate_fresh`) |
| Candidate OWLAPI adapter | KM 1.5.3 | `ecc4b1c57bc799bd8b2cf501fb5c2921607d9051` | `fa6d4c6aa97da3811bc411ab51d597d25c1a8d31e333383599ef13be916b10be` (JAR), `19f6903a6b680ff5bb1b4bbd038b2c3c02ea94797f92b48ce3baffecb7523e33` (compile receipt) | Maven, JDK 17.0.20.1+1; retained and fresh OWLAPI sessions |
| Released baseline, retained and fresh | KM 1.5.0 | `d95f0b840a433b5b43c4eff48092e8b600bca8de` | `1dbc0dd92170abcd70e948fa2dc2d9d13d5c72076bcff9ad7a664921188e5900` | Published profile-use executable and v1.5.0 Java adapter (`released_baseline_retained` and `released_baseline_fresh`) |
| Prior release reference | KM 1.5.2 | `860d2a41861554c4ec2966d961781b87c6c732ee` (impl `1f4fb91e61ae072aa64ad6d8ca58732a77e90a59`) | `5bdced8e7926686927799b61549cdc19e122487d36d32f58d48a25d064c0662b` (native), `25f9f66f7f7164225f65cfc04ab8c335b3f25f394a9153a45dec942370cc0053` (JAR) | Prior non-PGO release reference |
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
`protege/` trees match commit `ecc4b1c57bc799bd8b2cf501fb5c2921607d9051` with an
empty tree diff. The annotated `v1.5.3` tag, `BENCHMARKS.md`, and
`build-completion.json` identify the exact final release commit. No abbreviated
commit serves as a source binding.

## 1,920-ontology total static classification benchmark

The total static classification benchmark evaluates `km classify` across the
frozen 1,920-ontology corpus (`full-candidate-inputs.json`, SHA-256
`0309377d05dfd0cd81eb46050416272fbd52b16e77f21d9a37d732b352817fb4`), comprising
`1,708` admitted `checks_passed` ontologies and `212` `invalid_input` expected
refusals under a 240-second timeout, 20,480 MiB process-tree RSS limit, and
single-core execution (`KM_THREADS=1`, `RAYON_NUM_THREADS=1`, `OMP_NUM_THREADS=1`)
on IBEX `cpu_intel_gold_6248` (Intel Xeon Gold 6248 @ 2.50 GHz).

KM 1.5.3 (`2470b0415f1a78533024e15b5c317f9e743a98916b597739db93b9452a8dd8d4`) solves
`1,662 / 1,708` admitted ontologies verified against the four independent
correctness reference reasoners (`konclude`, `hermit`, `openllet`, `jfact`),
refuses `212 / 212` invalid inputs with exit code 2 (`0` unresolved), and produces
`0` taxonomy differences across all `1,663` common completed classifications
compared against released KM 1.5.0
(`1dbc0dd92170abcd70e948fa2dc2d9d13d5c72076bcff9ad7a664921188e5900`). Across all
`1,662` verified completions, KM 1.5.3 achieves `2.6581 s` mean and `0.1377 s`
median wall time (`218.23 MiB` mean peak RSS, `56.27 MiB` median peak RSS),
beating Konclude (`2.9232 s` mean, `0.2690 s` median across `1,655` solved),
KM 1.5.0 (`3.2557 s` mean, `0.2305 s` median across `1,661` solved), KM 1.5.2
(`5.6605 s` mean, `0.3209 s` median across `1,660` solved), RustDL `v0.4.41`
(`8.5060 s` mean, `0.6576 s` median across `1,428` solved), RustDL `v0.4.28`
(`5.1386 s` mean, `0.3312 s` median across `1,212` solved), and ELK `v0.6.0`
(`11.9712 s` mean, `4.7772 s` median across `1,411` solved) on both all-verified
and common-verified intersections.

| Method | Version / commit | Verified solved / 1,708 | All-verified mean / median (s) | Common verified with KM 1.5.3 | KM 1.5.3 common mean / median (s) | Competitor common mean / median (s) | KM 1.5.3 gained / lost |
|---|---|---:|---:|---:|---:|---:|---:|
| KM 1.5.3 (candidate) | `v1.5.3` / `ecc4b1c57bc7` | 1,662 | 2.6581 / 0.1377 | 1,662 | 2.6581 / 0.1377 | 2.6581 / 0.1377 | 0 / 0 |
| KM 1.5.0 (released baseline) | `v1.5.0` / `d95f0b840a43` | 1,661 | 3.2557 / 0.2305 | 1,661 | 2.6574 / 0.1374 | 3.2557 / 0.2305 | 1 / 0 |
| KM 1.5.2 (prior release) | `v1.5.2` / `1f4fb91e61ae` | 1,660 | 5.6605 / 0.3209 | 1,660 | 2.5969 / 0.1373 | 5.6605 / 0.3209 | 2 / 0 |
| Konclude | `v0.7.0-1138` / `0002e8063540` | 1,655 | 2.9232 / 0.2690 | 1,642 | 2.1246 / 0.1336 | 2.9334 / 0.2671 | 20 / 13 |
| RustDL (updated latest) | `v0.4.41` / `7bf5af7e1b13` | 1,428 | 8.5060 / 0.6576 | 1,419 | 1.0699 / 0.1050 | 8.3728 / 0.6257 | 243 / 9 |
| RustDL (v1.5.0 baseline) | `v0.4.28` / `b120b1783dc8` | 1,212 | 5.1386 / 0.3312 | 1,205 | 1.0381 / 0.0979 | 5.0630 / 0.3183 | 457 / 7 |
| ELK | `v0.6.0` / `b8ac5ce83db0` | 1,411 | 11.9712 / 4.7772 | 1,399 | 1.7085 / 0.1061 | 11.7327 / 4.7464 | 263 / 12 |

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
1. `candidate_retained`: KM 1.5.3 persistent session (`km incremental-source` on CLI;
   retained `KMReasoner` with `BUFFERING` flush on OWLAPI).
2. `candidate_fresh`: KM 1.5.3 fresh classification from scratch on each revision
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
enforced by the scoped process-tree watchdog (`ScopedSnapshot`). Every invocation
runs inside a Linux `PR_SET_CHILD_SUBREAPER` scope that verifies zero surviving
descendant processes before and after each arm (`cleanup_proven_empty: true`).

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
`ore_ont_16744`, KM 1.5.3 (`candidate_retained` and `candidate_fresh`) completes
all nine revisions across all five repetitions on both CLI and OWLAPI, whereas
KM 1.5.0 times out on updates 7 and 8 on CLI and at initialization on OWLAPI; on
OWLAPI, KM 1.5.0 also has baseline non-completions on `ore_ont_10689` and
`ore_ont_15703`, while KM 1.5.3 completes all five repetitions of both. Both the
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

## Key technical changes in v1.5.3

1. **Copy-on-write node resolution storage and single-word clause head bitsets**:
   `engine/src/tableau.rs` replaces eager per-node resolution vector clones with
   copy-on-write storage, and `engine/src/clause.rs` packs clause head bitsets into
   a single machine word when the signature fits, reducing allocation pressure and
   branching overhead during hypertableau and consequence-based saturation.
2. **Classifier-owned atomic ABox projection and refined HT routing guards**:
   `engine/src/abox_project.rs`, `engine/src/routing.rs`, and
   `engine/src/orchestrate/runner.rs` extend atomic ABox projection across the
   screened nominal-free object fragment and anonymous individuals, retry compact
   EL-ABox fallback in-memory without reloading the ontology from disk, and refine
   HT bridge-first and certified-nominal routing guards. This recovers
   `ore_ont_8509` in `4.02 s` and accelerates heavy ABox and bridge ontologies.
3. **Fast integral decimal screening and PGO release build**:
   `engine/src/frontend/conformance.rs` adds a fast path for integral decimal
   lexical screening during upfront conformance validation, and the release
   executable is compiled with profile-guided optimization (`-Cprofile-use`) over
   the representative classification and incremental workload.

## Correctness and certification

For each measured revision, canonical taxonomy hashes and consistency are checked
across all completed arms (`0` differences across all 7,110 candidate-pair revision
checks). All four production Lean certification gates (`elc`, `routing`, `ht`, `cb`)
are executed from the exact tagged release commit with zero `sorryAx`, alongside the
full 45-command serial Rust CI test suite (`3,120` passed, `0` failed) and the
76-test Maven Java suite.

## Reproducing and inspecting the release

Build the tagged source using `cargo build --locked --release --features mimalloc
--bin km` in `engine/` (with `RUSTFLAGS="-Cprofile-use=merged.profdata
-Cllvm-args=-pgo-warn-missing-function"` for the profile-guided build). Reproduce
the JAR with `mvn package` in `protege/`.

The release attaches:
- `km-v1.5.3-linux-x86_64`: the measured native executable.
- `kobayashi-marust-protege-1.5.3.jar`: the measured Protégé / OWLAPI package.
- `km-v1.5.3-certified-source.tar.gz`: the exact final source archive.
- `BENCHMARKS.md`: final results, including per-case and per-update tables.
- `build-completion.json`: machine-readable results and certification bindings.
- `SHA256SUMS`: checksums of the other five files.

Download all files into one directory and run `sha256sum -c SHA256SUMS`. The
annotated `v1.5.3` tag binds the manifest by its HTTPS location and SHA-256.
