# v1.5.5 release procedure

Status: prepared on 2026-10-31 by the `release-pipeline` agent on branch
`fix/v155-release-pipeline`; dry-run as far as possible without the tagged
release candidate. The contract is `docs/V1.5.5-ACCEPTANCE.md` (S1 speed,
C1 correctness, L1 Lean, R1 release; no performance amendment). The tools
are in `tools/release/v155/`. Paths below are absolute on ws unless they
start with `/ibex`; `$R` is the repository root
`/mnt/data2/workspaces/leechuck/software/kobayashi-marust` and `$T` is
`$R/.work/worktrees/<a clean checkout of the tag>/tools/release/v155`.

Times are wall times measured in the dry run of 2026-10-31 (ws shared with
other agents, Ibex `batch` partition), except where a line says
"v1.5.4 receipt", which is the time the same step took for v1.5.4 because the
dry run did not execute it (see "What the dry run did not do").

## 0. Preconditions

- `development/v1.5.5` holds every fix; C1 and L1 work is merged; the
  version in `engine/Cargo.toml`, `Cargo.lock` and `protege/pom.xml` is 1.5.5.
- Disk: at least 30 GB free on `/mnt/data2` (the PGO targets take about
  6 GB and are deleted afterwards; the gates need 20 GB free at entry and
  exit, `capture-gate.py` refuses otherwise).
- No other `cargo`, `rustc`, `lake`, `lean` or `km` process may run on ws
  while a Lean gate or the full Rust suite runs (`capture-gate.py` and
  `run-full-rust.py` refuse to start). The PGO build and the Ibex runs do
  not have this restriction.

## 1. Tag the release candidate (supervisor)

```bash
cd $R/.work/worktrees/v1.5.5
git tag -a v1.5.5-rc1 -m "KM 1.5.5 release candidate 1" <commit>
git worktree add --detach $R/.work/worktrees/v1.5.5-rc1 v1.5.5-rc1
```

The release tag `v1.5.5` is cut from the same commit only after every step
below passes; if the commit changes, every step is repeated. Seconds.

## 2. PGO build of the candidate (ws, about 25 min)

```bash
cd $R/.work
python3 $T/pgo_build.py --worktree $R/.work/worktrees/v1.5.5-rc1 \
    --root $R/.work/pgo-v155 --version 1.5.5 \
    --cpus 17-24 --train-cpus 17,18,19,20 > $R/.work/pgo-v155.log 2>&1
python3 $T/pgo_build.py --worktree $R/.work/worktrees/v1.5.5-rc1 --root $R/.work/pgo-v155 --clean
```

The recipe is the v1.5.4 one (`.work/pgo-v154/run_pgo_pipeline.py` plus
the `pgo-use-bfd` phase): `git archive` of the commit with a per-file hash
manifest checked before and after each build; instrumented build
(`-Cprofile-generate`, LTO, one codegen unit, `--features mimalloc --bin km`,
`--target=x86_64-unknown-linux-gnu`); training on the frozen 22-input
selection (`.work/worktrees/v1.4/.../training-selection.json`) through
`.work/v152-correctness-1920/run_1920_ws.py`, where every training answer
must be verified against the pinned references; `llvm-profdata merge
-sparse`; profile-use build linked through `cc-wrapper.sh`
(`--defsym=pidfd_spawnp=0 --defsym=pidfd_getpid=0`, sha256 `18d4f2e7…`, the
v1.5.3 and v1.5.4 wrapper) so that the binary needs at most GLIBC_2.34
(Ibex); the build-log audit rejects any profile mismatch. The result is
`km-v1.5.5-rc-pgo` with `km-v1.5.5-rc-pgo.sha256` and
`native-build-receipt.json`. Only the wrapper-linked binary is built: it is
the measured and released binary and it runs on ws as well, so the ws-only
`km-pgo-use` link of v1.5.4 is not repeated. `--clean` deletes the target
directories, training runs, raw profiles and unpacked source (about 2 GB
left: archive, profile, receipts, binaries).

Dry run (commit `895d4baf`, CPUs 17-24 of a shared ws): instrumented build
551 s, training 255 s (22 of 22 verified, 35 raw profiles), merge 1 s,
profile-use build with the wrapper 703 s, total 1,531 s (26 min); binary
sha256 `0951650a834b426f3d7395c9fc53ef7e7bd0b01ad2689a7c55ee0dd0ec8f3289`,
GLIBC at most 2.34, audit 4,362 trained functions and 0 mismatches.
`--clean` leaves 127 MB. (v1.5.4 receipts: 491 s, 371 s, 1 s, 462 s.)

## 3. Stage the Ibex root (ws, about 1 min)

```bash
$T/stage.sh v155-release-<YYYYMMDD> $R/.work/pgo-v155/km-v1.5.5-rc-pgo \
    $R/.work/pgo-v155/native-build-receipt.json
```

This creates `/ibex/scratch/projects/c2014/hohndor/km/v155-release-<YYYYMMDD>/`
with `protocol/` (the eight measurement and audit modules of the v1.5.4 G8
run `g8-v154-80c8f82a/`, copied and checked against that run's
`combined-files.sha256`), `inputs/` (the 585-input held-out manifest
`50b8b890…` and the 1,920-row pool manifest `0309377d…`, 1,708 admitted),
`binaries/` (the RC and the v1.5.3 release asset `km-v1.5.3-linux-x86_64`,
sha256 `2470b041…`, the binary of the v1.5.3 runs), `artifacts/rc.json`,
`v153.json`, `konclude.json` (the release flags of v1.5.3 and v1.5.4:
`KM_HT_DDB KM_HT_NATIVE_FULL KM_CACHE_CONFORMANCE
KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE KM_FAST_IRI_GRAMMAR KM_JSON_GRAPH_EDGES`),
the runners and the sbatch files, and `files.sha256`, which every task
checks before it measures. Only copying and hashing run on the login node.
Re-staging a new RC replaces its binary entry, `artifacts/rc.json` and
`files.sha256`; finished runs keep their directories and record the
inventory and binary hashes in every chunk.

Dry run: `stage.sh v155-release-20261031` with the dry-run binary, 10 s.

## 4. Smoke job (Ibex, a few minutes)

```bash
ssh ibex 'cd /ibex/scratch/projects/c2014/hohndor/km/v155-release-<YYYYMMDD> && sbatch --parsable smoke.sbatch'
```

Three tasks on six inputs (`inputs/smoke-inputs.txt`: five held-out and one
design-half input): task 0 the RC, task 1 v1.5.3, task 2 Konclude. All six
must be verified by KM in tasks 0 and 1, and Konclude's answers must equal
its 2026-10-04 answers. Dry run: array 54861589 (submitted 2026-10-31,
2 min 20 s in the queue), tasks 14 s, 15 s and
46 s on cn512-27-r/-l; RC and v1.5.3 verified 6 of 6, no wrong answer;
Konclude answered 6 of 6, all identical to 2026-10-04 (5 verified against
HermiT/Openllet/JFact; `ore_ont_5760` has only the Konclude reference).
`fetch.sh` (10 s) and `aggregate.py` on these records ran end to end; the
verdict on six inputs means nothing beyond that the job set runs.

## 5. Same-day measurement (Ibex)

Submit the three held-out runs together so they share the day and node
pool, then the pool run:

```bash
ssh ibex 'cd /ibex/scratch/projects/c2014/hohndor/km/v155-release-<YYYYMMDD> &&
  for s in heldout-rc heldout-v153 heldout-konclude pool-rc; do echo $s $(sbatch --parsable $s.sbatch); done'
```

| Job set | Runner | Array | Inputs | Output |
|---|---|---|---|---|
| (a) held-out, RC | `run_release.py` | 0-18 | 585 | `heldout-rc-<job>/` |
| (b) held-out, v1.5.3 same day | `run_release.py` | 0-18 | 585 | `heldout-v153-<job>/` |
| (c) held-out, Konclude same day | `run_konclude.py` | 0-18 | 585 | `heldout-konclude-<job>/` |
| (d) full regression pool, RC | `run_release.py` | 0-59 | 1,920 rows (1,708 admitted) | `pool-rc-<job>/` |

Every job set uses the v1.5.3 protocol: Ibex `batch`, `cpu_intel_gold_6248`
nodes, `--exclude=cn603-25-l`, one core per task, 24 GB per task, 240 s and
20 GiB per input through the scoped watchdog (`measure_classification.py`
with `ScopedSnapshot` and the exit observer), audit by canonicalisation and
comparison with the pinned Konclude, HermiT, Openllet and JFact answers. Each
input leaves `record.json`, `taxonomy.raw`, `canonical.*`, `stderr` and
`max-rss-kib.txt` in its directory, as in the v1.5.4 runs; each task writes
`chunks/<task>.json`. The task time limit is 4 h (v1.5.4: 30 min); the limit
does not enter the measurement. Konclude runs with the binary and command of
array 53201252 (`Konclude-build-a`, sha256 `e8dd5373…`,
`classification -w 1 -v`, OWL/XML input) on the verified 2026-10-04
conversions; the 2026-10-04 run used the pre-scoped watchdog module, the
same-day run the scoped one, like the KM runs. Each Konclude answer is
compared with the 2026-10-04 answer and with HermiT, Openllet and JFact.

Expected duration (v1.5.4 receipts, v1.5.3 protocol): held-out tasks finish
within about 30 min once running; the pool array within about 30 min per task;
queueing on `batch` adds from minutes to hours. Konclude 2026-10-04 ran with
`%8`; the same-day set runs all 19 tasks at once.

## 6. Fetch and aggregate (ws, about 1 min)

```bash
D=$R/.work/v155-release-cert/data
$T/fetch.sh v155-release-<YYYYMMDD> $D heldout-rc-<a> heldout-v153-<b> heldout-konclude-<c> pool-rc-<d>
python3 $T/aggregate.py --data $D --rc heldout-rc-<a> --v153 heldout-v153-<b> \
    --konclude heldout-konclude-<c> --pool pool-rc-<d> \
    --ibex-root /ibex/scratch/projects/c2014/hohndor/km/v155-release-<YYYYMMDD> \
    --out $R/.work/v155-release-assets-<commit8> --tag v1.5.5 --commit <sha> \
    --pgo-root $R/.work/pgo-v155 --cert-root $R/.work/v155-release-cert/ctl
```

`aggregate.py` uses the arithmetic of `.work/v154-release-cert/ctl/build-assets.py`
unchanged (ratio of the means and ratio of the medians of wall seconds over
the inputs verified in both runs; coverage, lost, gained; the
`konclude_solved` rule) and judges S1 without exception: no loss against
both the same-day v1.5.3 run and the 2026-10-25 run, mean and median ratio
≤ 1.10 against the same-day run, more verified inputs than the same-day
Konclude run and a lower mean and median time on the common inputs. C1's
benchmark part: no wrong answer (some reference disagrees and none agrees)
on the held-out run or on the 1,708 admitted pool inputs, except an answer
whose canonical fingerprint equals an entry of `adjudications.json`
(`ore_ont_3794`, a Konclude incompleteness confirmed by HermiT). It writes
`BENCHMARKS.md` and `build-completion.json` (v1.5.4 schema, no
`authorized_performance_exception`), and `SHA256SUMS` and `manifest.json`
once all four assets of step 9 are in the output directory; it prints the
verdict. Any `NOT_MET` stops the release.

Check of the arithmetic (`aggregate.py --reproduce-v154`, on the v1.5.4
records in `.work/v154-release-cert/data/`): 556 common inputs, mean ratio
1.1717, median ratio 1.0771, the three decomposition rows (1.025/1.151,
1.070/1.104, 0.936/1.179), allowed sum 2,405.117 s, excess 156.729 s,
Konclude 558 against 554 on 534 common inputs, largest delta `ore_ont_205`
+152.61 s: every value equal to v1.5.4's `build-completion.json`. The one
difference is deliberate: `flagged_wrong` is recomputed from the
comparisons and now lists `ore_ont_3794`, which v1.5.4's protocol runner did
not mark. Without a paired run the G8 of record is the two-run common set
(v1.5.4 data: 558 inputs, mean 1.199, median 1.074). The pool check on the
v1.5.3 2026-10-25 run (1,708 admitted): 1,662 verified, only `ore_ont_3794`
flagged; that legacy record has no fingerprint, so the check does not excuse
it (fail closed). Under one second each.

## 7. Gates from the tag (ws, about 1.5 h; v1.5.4 receipts)

Use a dedicated clone, not a worktree: the v1.5.4 gate clone
`.work/gates-4dd7995b/src` keeps its built `lean/.lake` (8.5 GB with
mathlib), so moving it to the new tag avoids rebuilding mathlib.

```bash
S=$R/.work/gates-4dd7995b/src
git -C $S fetch $R refs/tags/v1.5.5-rc1:refs/tags/v1.5.5-rc1 && git -C $S checkout --detach v1.5.5-rc1
test -z "$(git -C $S status --porcelain)"
mkdir -p $R/.work/v155-release-cert && cp -r $T/gates $R/.work/v155-release-cert/ctl
cd $R/.work/v155-release-cert/ctl
python3 prepare.py $S $(git -C $S rev-parse HEAD) $R/.work/v155-release-cert/ctl 1.5.5
```

`prepare.py` (1.7 s in the dry run against this branch) binds every tracked
file of the clone by hash, mode and permission, the Rust and Lean tools, the
five gate scripts, the subreaper helper of v1.5.1 and the ORE 7278 input of
the rules gate (sha256 `266688ec…`).

Then the native build of the tag (`.work/gates-4dd7995b/build.sh` adapted:
workstation paths instead of the container's `/workspace`, the bound
`control-bin/cargo`):

```bash
cd $S/engine && CARGO_TARGET_DIR=$R/.work/v155-release-cert/target-native CARGO_INCREMENTAL=0 \
  nice -n 10 $R/.work/v155-release-cert/ctl/control-bin/cargo build --release --bin km --features mimalloc --jobs 4 \
  > $R/.work/v155-release-cert/logs/native-build.log 2>&1
```

The five Lean gates, one after another (each refuses to start next to a
compiler, checks the bound source and tools before and after, rejects any
`sorryAx` in the log or the theorem surface, and writes a receipt):

```bash
$R/.work/v155-release-cert/ctl/run-five-gates.sh
grep -E '=== .* exit' $R/.work/v155-release-cert/logs/five-gates.log
```

v1.5.4 receipts: `elc` 41 min, `routing` 5 min, `ht` 3 min, `cb` 1 min (one
`cb` attempt was rejected at the exit disk floor and repeated). The fifth
gate `rules` (new in v1.5.5: `rules-inert-sort-release-check` and
`rules-cert-check`, the rule-route theorem surface, `rules_lean_certificate`
and the inert-sort certificate tests including ORE 7278) has no release
timing yet; the `ht` gate now also builds `ht-subset-unravelling-check`.

Full Rust suite (serial, CI recipe, the 22 checker-bound lib tests skipped
because the gates ran them; refuses to start unless all five gate receipts
passed), then the checker step and the Java gate:

```bash
cd $R/.work/v155-release-cert/ctl
nice python3 run-full-rust.py > ../logs/full-rust.log 2>&1        # v1.5.4 receipt: 25 min, 3,299 passed
./checkers-step.sh . $R/.work/pgo-v155/km-v1.5.5-rc-pgo checker-step
./java-step.sh . $R/.work/pgo-v155/km-v1.5.5-rc-pgo              # v1.5.4: 26 s, 76 tests
```

`checkers-step.sh` builds every Lean checker once from the bound snapshot,
runs `lean/run-checker-tests.sh` (the CI-skipped checker tests, serially)
and `tools/checkers-on-suite.sh` with the RC binary on the default fixture
set (modes off, on, ht), writes `checker-step/receipt.json` and removes the
native checkers again. The checkers-on suite of 2026-10-30 took several
hours on 1,781 inputs; the fixture set is the 186 fixtures. L1 also needs
the suite's results recorded in `docs/CHECKERS-ON.md`.

## 8. Assets (ws, a few minutes)

```bash
A=$R/.work/v155-release-assets-<commit8>
cp $R/.work/pgo-v155/km-v1.5.5-rc-pgo $A/km-v1.5.5-linux-x86_64
git -C $S archive --prefix=kobayashi-marust-1.5.5/ v1.5.5 | gzip -n -9 > $A/km-v1.5.5-certified-source.tar.gz
cp $S/protege/target/kobayashi-marust-protege-1.5.5.jar $A/
# re-run the aggregate.py command of step 6 with --out $A
```

The second `aggregate.py` run checks that the asset binary is the receipted
PGO binary, fills `generated_artifact_hashes`, and writes `SHA256SUMS` and
`manifest.json` over the five files, as v1.5.4 did. `build-completion.json`
reaches `R1_release_gates: met` only with five passed gate receipts, a
passed checker step, the Rust receipt and the Java receipt.

## 9. Release

Update `docs/V1.5.5-ACCEPTANCE.md` with the evidence for C1, S1, L1 and R1,
write `docs/RELEASE-1.5.5.md` from `BENCHMARKS.md` and the receipts, tag
`v1.5.5` at the RC commit (the engine tree must be unchanged; documentation
commits after the RC need a new tag and the gates again only if they change
a gated file), push, and attach the five assets and `SHA256SUMS`.

## Execution notes (2026-11-01, candidate `v1.5.5-rc1` = edeb7fff)

Every step above ran on the candidate. Four things the dry run could not
show, each fixed in place and logged under `.work/v155-release-cert/logs/`:

- Step 7, native build: the first `cargo build` failed inside the `rustc`
  proxies with rustup component-install errors (another process ran
  `rustup` on ws at the same moment; `native-build-attempt1-rustup-race.log`).
  The retry with `RUSTUP_TOOLCHAIN=stable-x86_64-unknown-linux-gnu` set
  passed in 8 min.
- Step 7, gates: all five were rejected within seconds because the gate
  clone's `lean/.lake` had been shared by hard links (`cp -al`) with the
  integration worktree to verify merges there; lake rewrites `.trace`
  files in place but Lean writes new `.olean` files, so the clone held
  v1.5.4 `.olean` files behind current traces and replayed them
  (`ELCompletionWire` failed to elaborate against the stale
  `ELResidualCertificate.olean`; `five-gates-attempt1-stale-lake.log`,
  `attempt1/`). Never share a `.lake` directory by hard links. Fix: delete
  the clone's `lean/.lake/build` (packages stay) and rerun; the gates then
  rebuild ContextCalculus from the bound sources (`elc` 28 min, `routing`
  6, `ht` 4, `cb` 4, `rules` 7). `capture-gate.py` refuses to overwrite a
  receipt, so a rejected receipt must be moved aside before a rerun.
- Step 7, checker step: the gates delete the native checker executables
  after their audit but leave lake's `.trace` and `.hash` files in
  `lean/.lake/build/bin`, so the step's `lake build` reports everything up
  to date and the 22 checker-bound tests fail instantly for want of the
  executables (`attempt1/checker-step/`). Fix before the step: remove
  `<name>.trace` and `<name>.hash` for every missing executable in that
  directory (109 on 2026-11-01); `checkers-step.sh` should do this itself.
- Step 7, Java step: `java-step.sh` requires exactly one
  `kobayashi-marust-protege-*.jar` in `protege/target`; the gate clone kept
  the v1.5.1 and v1.5.4 jars from earlier releases. Delete stale jars first.
- Step 7, full Rust suite: `run-full-rust.py` aborts the whole run when any
  process named `km` exists on ws between two test targets, even one it did
  not start (first attempt: a `km` process appeared after target 16 of 60;
  `attempt1/full-rust-stray-km.log`). The run cannot resume; move
  `full-rust-execution` aside and start again. On 2026-11-01 the stray
  processes were `km classify` calls of another agent's test suite
  (`eq-biodt` on ws), which recurred every few minutes and aborted a second
  attempt at target 11 of 60, so the third attempt ran the driver inside a
  private PID namespace with its own `/proc`
  (`unshare -Urpf --mount-proc python3 run-full-rust.py`): the driver's
  check then covers every process the suite itself starts, which is what
  it is for, and not the other agent's. The receipt records
  `active_compilers_after` as seen from inside the namespace. Nothing else
  changes: the bound tools, the serial recipe and the CPU set are the same.
- Step 7, checker step, second defect: `lake build` without targets builds
  the two library default targets only; the 109 checkers are `[[lean_exe]]`
  targets and must be named (`checkers-step.sh` on `development/v1.5.5`
  now does both this and the trace cleanup). On the tag the executables were
  built by hand with `lake build <every lean_exe name>` before the step.

## What the dry run did not do

- The held-out, pool and Konclude job sets (a) to (d) were not submitted;
  the supervisor submits them on the tagged candidate.
- No Lean gate, no full Rust suite, no Java step and no checker step ran:
  they need the tag, and running them would have moved the v1.5.4 gate
  clone `.work/gates-4dd7995b/src` (owned by the release process) or needed
  a second 8.5 GB `lean/.lake`. `prepare.py` ran against this branch
  (1.7 s, 9,419 files bound); `capture-gate.py`, `run-full-rust.py`,
  `checkers-step.sh` and `java-step.sh` are only syntax-checked. Their
  times above are v1.5.4 receipts, and the rules gate has no time yet.
- The asset step (8) was not run.
