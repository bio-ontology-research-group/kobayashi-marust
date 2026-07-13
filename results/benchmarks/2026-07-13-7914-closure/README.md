# ore_ont_7914 closure and plan-15 regression sweep

Status: complete. This directory records the exact Konclude comparison that
closed `ore_ont_7914`, the first 592-ontology ORE 2015 sweep, the controlled
regression diagnosis, the 5303 repair, and the final 592-ontology IBEX sweep.

Binary identities:

- native 7914 closure binary:
  `69ad7080fb010428aaa7ee617f61520d274eb95f0b33dcf9d6726507ae1e2fc1`;
- first Bullseye-linked sweep binary:
  `4e8e4b160cf1ac61c12a8b3c3e4b21d0c2b6218d97b0a24642178f3021e32b69`;
- final Bullseye-linked binary after the 5303 regression repair:
  `8f31f40548b76815f91ec48b417d8a026a454401aaa9e173ec5d1df3d838eb17`.

The final binary requires at most GLIBC 2.29. IBEX smoke job 48737774 matched
5303 exactly and matched 7914 in 78 seconds at 15,379,188 KB.

## Full-sweep result

Both sweeps ran one ontology per task with 240 seconds, 20 GB, and the exact
trigger-absorption feature flags used for the closure run.

| IBEX job | Scope | ok | timeout | match | incomplete | unsound | both | incons | no-gold |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 48736902 | first feature-enabled sweep | 570 | 22 | 498 | 52 | 10 | 2 | 6 | 2 |
| 48737778 | final sweep after 5303 fix | 569 | 23 | 499 | 50 | 10 | 2 | 6 | 2 |

Relative to the first feature-enabled sweep, 5303 is the only signature
change: one missing pair became an exact gold match. No gold-matching ontology
regressed. The one-run status difference on 9663 does not reproduce as a code
difference. The pre-fix feature binary and final binary both timed out at a
300-second diagnostic cap, with peak RSS 17,312,252 and 17,321,180 KB.

The apparent regressions against the preceding default-config sweep mostly
measure the enabled feature configuration, not this code change. Same-flags
controlled jobs 48737880 and 48738400 cover 18 ontologies and report zero
old-versus-final result changes, zero controlled regressions, and zero
controlled improvements. The recoveries against the preceding default sweep
remain 16444, 2497, and 7914.

The final aggregate is stored on IBEX as
`plan15_7914_closure/aggregate-final.json` (SHA-256
`349bca0cb550ea7251713832a0241857edbb2e729c89a984f9adc9ac66d0eca4`).
The full causal account is in `docs/SOLVE-7914-9663-9724.md`;
`final-summary.json` records the portable result in a small machine-readable
artifact.

## Reproduction scripts

- `ibex_plan15_fullsweep.sbatch` runs one ontology per IBEX array task. Its
  `KM_SWEEP_BINARY`, `KM_SWEEP_CONFIG`, `KM_SWEEP_RESULT_DIR`, and
  `KM_SWEEP_OUTPUT_DIR` overrides keep successive sweeps separate.
- `ibex_plan15_regression_ab.sbatch` runs the same flags on two binaries. It
  accepts explicit previous/candidate paths, a result suffix, and a diagnostic
  timeout override.
- `aggregate_ibex_plan15.py` compares all candidate records with Konclude gold
  and reads an alternate result directory from `KM_SWEEP_RESULT_DIR`.

## Direct 7914 closure evidence

| Slurm job | Scope | Wall | Peak RSS | Subsumptions | Konclude comparison |
|---|---:|---:|---:|---:|---|
| 7934 | subject 9180, `UBERON_0003657` family | 2:05.20 | 18,916,764 KB | 141,517 | agree, 0 extra, 0 missing |
| 7935 | subject 852, `UBERON_0010961` family | 2:05.03 | 18,936,060 KB | 141,517 | agree, 0 extra, 0 missing |
| 7936 | full ontology, all 93 residue subjects | 2:30.56 | 18,882,684 KB | 141,517 | agree, 0 extra, 0 missing |

The full run completed all 93 residue subjects in round 0 with no deferred or
permanently deferred subjects. `sig_cmp.py` reported `gold_match: true`, zero
unsound subsumptions, zero incomplete subsumptions, no unsatisfiable-class
differences, and no consistency mismatch.

IBEX array 48736526 was an infrastructure-only failed attempt and was
cancelled. The native `ws` binary required GLIBC 2.39, while IBEX does not
provide it. No reasoning task started. The source was rebuilt on `ws` in the
official Rust 1.85 Bullseye container with an isolated target directory; the
result requires at most GLIBC 2.29.
