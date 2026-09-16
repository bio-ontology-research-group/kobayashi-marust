#!/bin/bash
#SBATCH --job-name=km-v14-min-head-int-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:25:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v140-release-final-20260916/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v140-release-final-20260916
archive=$root/source.tgz
expected=211852a77a8b90a0e710910500cabe4f7b1bd1ced7f35a28d79c846eee91077d
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
build=$root/source-$SLURM_JOB_ID
target=$root/target-$SLURM_JOB_ID
mkdir -p "$build"
tar -xzf "$archive" -C "$build"
cd "$build/engine"
CARGO_TARGET_DIR="$target" cargo build --release --locked --bin km
cp "$target/release/km" "$root/km.ibex"
{
  printf 'source_archive_sha256\t%s\n' "$expected"
  printf 'binary_sha256\t%s\n' "$(sha256sum "$root/km.ibex" | cut -d' ' -f1)"
  printf 'host\t%s\nslurm_job_id\t%s\nZ\tcomplete\n' "$(hostname)" "$SLURM_JOB_ID"
} > "$root/build-receipt.tsv"
