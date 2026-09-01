#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --job-name=km-paper-incremental-v13
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/incremental-v13-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
runtime=/ibex/scratch/hohndor/km/v1.3.0-candidate-5c64a02/km
runner=$root/runner-tools/incremental_v13_benchmark.py
out=$root/incremental-v13
expected_binary=cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d
expected_runner=8086d06639bd16dcde6fb9d806aabf6e4825612e21d3f60b5fbb1628f2492c3d

cpu_model=$(awk -F ': ' '/model name/{print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
test "$(sha256sum "$runtime" | awk '{print $1}')" = "$expected_binary"
test "$(sha256sum "$runner" | awk '{print $1}')" = "$expected_runner"
mkdir -p "$out"

/usr/bin/python3 "$runner" --binary "$runtime" \
  --warmups 1 --repetitions 10 --el-size 10000 --cb-chains 500 \
  --output "$out/results.json"

/usr/bin/python3 - "$out/results.json" <<'PY'
import json, sys
payload=json.load(open(sys.argv[1]))
assert payload["schema"] == 1
assert payload["binary_sha256"] == "cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d"
assert payload["runner_sha256"] == "8086d06639bd16dcde6fb9d806aabf6e4825612e21d3f60b5fbb1628f2492c3d"
assert payload["warmups"] == 1 and payload["repetitions"] == 10
for case, strategy in (("el", "el_delta"), ("cb", "cb_delta")):
    rows=payload["cases"][case]["measured_rows"]
    assert len(rows) == 10
    assert all(row["strategy"] == strategy and row["reused_fixpoint"] for row in rows)
    assert len({row["semantic_result_sha256"] for row in rows}) == 1
PY

{
  printf 'job_id\t%s\n' "$SLURM_JOB_ID"
  printf 'cpu_model\t%s\n' "$cpu_model"
  printf 'binary_sha256\t%s\n' "$expected_binary"
  printf 'runner_sha256\t%s\n' "$expected_runner"
  printf 'result_sha256\t%s\n' "$(sha256sum "$out/results.json" | awk '{print $1}')"
  printf 'complete\ttrue\n'
} > "$out/receipt.tsv.part"
mv "$out/receipt.tsv.part" "$out/receipt.tsv"
printf 'INCREMENTAL_V13_JOB_OK\t%s\n' "$SLURM_JOB_ID"
