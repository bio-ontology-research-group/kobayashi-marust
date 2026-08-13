#!/bin/bash
#SBATCH --job-name=km-7914-current-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/7914-regression-20260813/current-build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/7914-regression-20260813
archive=$root/source-53eb64a.tar.gz
expected=$(cat "$root/source-53eb64a.sha256")
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
src=$root/source-current-$SLURM_JOB_ID
mkdir "$src"
tar -xzf "$archive" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-current-$SLURM_JOB_ID
cd "$src/engine"
cargo build --release --locked --bin km --jobs 1
install -m 0555 "$CARGO_TARGET_DIR/release/km" "$root/bin/km-53eb64a.tmp"
mv "$root/bin/km-53eb64a.tmp" "$root/bin/km-53eb64a"
sha256sum "$root/bin/km-53eb64a" > "$root/bin/km-53eb64a.sha256"
echo BUILD_COMPLETE revision=53eb64a binary=$(cut -d' ' -f1 < "$root/bin/km-53eb64a.sha256")
