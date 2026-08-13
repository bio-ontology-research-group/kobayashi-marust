#!/bin/bash
#SBATCH --job-name=km-78d5674-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813
archive=$root/source-78d5674.tar.gz
expected=$(cat "$root/source.sha256")
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
src=$root/source-$SLURM_JOB_ID
mkdir "$src"
tar -xzf "$archive" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
cd "$src/engine"
cargo build --release --locked --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km.tmp"
"$root/km.tmp" routes >/dev/null
mv "$root/km.tmp" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
echo BUILD_COMPLETE revision=78d5674 binary=$(cut -d' ' -f1 < "$root/km.sha256")
