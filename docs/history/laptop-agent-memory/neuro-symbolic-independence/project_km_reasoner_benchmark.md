---
name: project_km_reasoner_benchmark
description: KM vs Sequoia vs HermiT time/memory benchmark setup on unimatrix01 (ORE 2015 ontologies)
metadata: 
  node_type: memory
  type: project
  originSessionId: 8013a140-9c7d-4310-a78e-c7c6c789bcd4
---

3-way reasoner time/memory benchmark for the KM contribution (NeSy paper, see [[project_nesy2026_revision_plan]], [[project_disjunction_headline_issue]]). User requested side-by-side vs Sequoia + HermiT (time + memory); run on unimatrix01.

**All three reasoners run on unimatrix01 under JAVA 8** (`/usr/lib/jvm/java-8-openjdk-amd64`; the cluster's java-11/21 are Graal-laden JREs without javac and broke sbt — Java 8 is clean and has javac):
- **HermiT**: `~/bench/Oracle.class` (compiled w/ java-8) + `~/bench/hermit_cp/*` (81 jars: hermit 1.4.6 + OWL API 5.1.9 deps, rsynced from local ~/.m2). Run: `java -cp ".:hermit_cp/*" Oracle <ont>` (emits JSON: consistent/subsumptions/unsatisfiable).
- **Sequoia**: built ON cluster from `~/Sequoia` (sbt 1.3.8 via `~/.sbt/launchers/1.3.8/sbt-launch.jar`, Scala 2.12.11, Java 8). Dist: `~/Sequoia/reasoner-cli/target/universal/sequoia-command-line-interface-0.6.1-alpha/`. Run: `java -cp "$DIST/lib/*" com.sequoiareasoner.cli.Sequoia classify <ont>`. **Sequoia = SRIQ only**: rejects nominals (ObjectOneOf) and ABox (ClassAssertion) and datatypes -> restricts the comparable ontology set.
- **KM**: `~/bench/km/kobayashi-marust` (Rust binary, runs fine on cluster glibc) + `~/bench/km/py/{owl_classify,frontend}.py`. Run: `KM_ENGINE=~/bench/km/kobayashi-marust PYTHONPATH=~/sroiq-rerun/pkg:~/bench/km/py ~/moose/.venv/bin/python owl_classify.py <ont>`.

**Ontologies:** ORE 2015 Reasoner Competition Corpus (Zenodo record 18578, 725MB, downloaded to `~/ore2015/`; CC-BY-NC-ND, benchmarking use). Files are OWL FUNCTIONAL syntax despite `.owl` ext -> all three parse them. Metadata: `~/ore2015/pool_sample/dl/classification/metadata.csv` (cols: expressivity, tbox/abox_nominals, abox_size, logical_axiom_count, class_count, ore2015_filename...). Selected 6 Sequoia-compatible (no nominals/ABox/datatypes) spanning 97->2821 axioms in `~/bench/ore/`: ore_ont_15399(AL,97) 8169(ALE+,155) 12007(AL,326) 5057(ALE+,778) 5940(ALCH,1611) 3931(SHIF,2821). Selector script: oracle/ore_select.py.

**Harness:** oracle/bench_reasoners.sh (SLURM `--exclusive`; /usr/bin/time -v -> wall + peak RSS; REPS=3 median; per-run `timeout` 900s). Writes `~/bench/results_*.csv`. Aggregate w/ /tmp/agg_bench.py (median per ontology x reasoner).

**FINAL RESULTS (medians, unimatrix01 exclusive nodes):**
3-way baseline (wall s / peak MB), KM=parallel: 15399(97ax) KM 0.14/18, Seq 2.25/273, Herm 1.26/178 | 8169(155) KM 0.22/18 | 12007(326) KM 0.21/20, Seq 2.38/276, Herm 1.52/228 | 5057(778) KM TIMEOUT(900s)/23, Seq 2.44/291, Herm 1.65/284 | 5940(1611) KM 42.6/26, Seq 2.51/307, Herm 1.72/315 | 3931(2821) KM 40.2(seq)->0.7(16thr)/49, Seq 2.99/419, Herm 2.35/618.
KM thread scaling (wall s) on 3931: T1=36.4 T2=15.7 T4=3.3 T8=1.3 T16=0.7 => ~52x (SUPER-linear: chunking also shrinks each engine's context registry/msg queue). 5057 times out at T1/2/4 alike = SINGLE-concept trivial-strategy explosion, parallelism can't help (honest limitation). Small onts parse-dominated (~0.1-0.2s flat).
HEADLINE: parallel KM BEATS HermiT+Sequoia on the largest ontology (0.7s vs 2.35/2.99s) at ~10x less memory (49 vs 419-618MB); KM wins memory everywhere (18-49 vs 178-618MB). One honest pathological case (5057). Jobs: baseline 4699/4702, scaling 4701.

**PARALLELIZED KM (2026-06-03, user request).** KM was single-threaded. The context calculus classifies each named concept via an independent root-context saturation; the shared successor context is only an OPTIMISATION, so each query's subsumptions are independent of which others are co-classified -> classification is embarrassingly parallel. Implemented at the driver level (verified saturation CORE untouched -> Lean soundness preserved): engine.rs `run()` refactored into `run_for(queries)` + `named_queries()`; reasoner.rs chunks the named concepts into `KM_THREADS` chunks and runs an independent `Engine` per chunk via rayon, merging (subsumptions union, inconsistent OR). Added `rayon` dep; `Sig` derives Clone. `KM_THREADS=1` forces sequential. VERIFIED: parallel output byte-identical to sequential on ORE ore_ont_12007; all 6 unit tests pass. New binary: cluster `~/bench/km/kobayashi-marust-par`. Scaling harness: oracle/bench_km_threads.sh (KM_THREADS in {1,2,4,8,16}). NOT yet committed/pushed; sroiq-nesy/rust-context-reasoner copy NOT yet synced (kobayashi-marust/engine is canonical). Trade-off: chunking loses cross-query successor sharing (modest redundancy, bounded by #chunks) for core-parallel speedup.

Also built (unused-by-default): synthetic SRIQ generator oracle/gen_sriq.py (number restrictions need SIMPLE role; min<=max to avoid unsat cascade) -- superseded by ORE per user.
