#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --job-name=km-impact-build

set -euo pipefail
: "${IMPACT_ROOT:?set IMPACT_ROOT}"
: "${SOURCE_COMMIT:?set SOURCE_COMMIT}"
source_root="$IMPACT_ROOT/source"
target_root="$IMPACT_ROOT/target"
mkdir -p "$target_root" "$IMPACT_ROOT/logs"
test -f "$source_root/engine/Cargo.toml"
cd "$source_root/engine"
test "$(git rev-parse HEAD)" = "$SOURCE_COMMIT"
export CARGO_TARGET_DIR="$target_root"
cargo build --release --bin km
binary="$target_root/release/km"
test -x "$binary"
{
  printf 'source_commit\t%s\n' "$SOURCE_COMMIT"
  printf 'binary_sha256\t%s\n' "$(sha256sum "$binary" | awk '{print $1}')"
  printf 'rustc\t%s\n' "$(rustc --version)"
  printf 'cargo\t%s\n' "$(cargo --version)"
  printf 'host\t%s\n' "$(hostname)"
  printf 'slurm_job_id\t%s\n' "$SLURM_JOB_ID"
} > "$IMPACT_ROOT/build-receipt.tsv"
