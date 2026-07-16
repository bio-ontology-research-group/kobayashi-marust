#!/bin/bash
# Lightweight CPU-only aggregation/training job. It reads only the small JSONL
# measurements and profile JSON, never the ontology corpus itself.
#SBATCH --job-name=km-route-analyze
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/analyze-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715
: "${EXPECTED_KM_SHA:?submit with the immutable km-profiled-atomic2 SHA-256}"
: "${EXPECTED_RUNNER_SHA:?submit with the frozen matrix runner SHA-256}"
: "${EXPECTED_PROFILE_SHA:?submit with the immutable profile-corpus SHA-256}"
profile_dir=${PROFILE_DIR:-$root/profiles}
analyzer=${ANALYZER:-$root/analyze_matrix.py}
runner_path=${RUNNER_PATH:-$root/bench_one_matrix_frozen.py}
results_glob=${RESULTS_GLOB:-$root/matrix-results-atomic3/*.jsonl}
output_dir=${OUTPUT_DIR:-$root/analysis}
/usr/bin/python3 "$analyzer" --root "$root" \
  --results-glob "$results_glob" \
  --profiles "$profile_dir" \
  --output-dir "$output_dir" \
  --expected-km-sha "$EXPECTED_KM_SHA" \
  --expected-konclude-sha 5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3 \
  --expected-elk-sha 8340bc1421c28aa5f0affff3a5533ef3f24f6cf19b3df7bbe43e237f7633600c \
  --expected-hermit-sha 389a119fa7b168e4fbb291850bcff8b5d39e5c59e4da1abea03544ddb8c3ccab \
  --expected-java-sha 854f27091cbf804f7fa6bfb2d958210740eb55e6d21f59d931f95a354a1a0619 \
  --expected-canonicalizer-sha 2fc28764e34418ae3004f6dca7bb9bb6c6f763b022b0d356b80f896fa18173a2 \
  --expected-profile-sha "$EXPECTED_PROFILE_SHA" \
  --expected-list-sha 7849b4b875d3b9bc5e214b67a1fa584f3d684e595954ca11a816448c87d3d2b8 \
  --expected-runner-sha "$EXPECTED_RUNNER_SHA" \
  --runner-path "$runner_path" \
  "$@"
