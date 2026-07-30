#!/bin/bash
# Build the production-meta correction from its exact committed archive.
#SBATCH --job-name=km-adaptive-comp-v2-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v2-20260731/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v2-20260731
tmp_root=${SLURM_TMPDIR:-$root}/build-$SLURM_JOB_ID
archive=$root/km-adaptive-comp-v2-c6bc65d.tar.gz
expected=1a3a850c51095da64253f23feceb4fe5f9d4805669fbdf8f4c2cc788f6e0b7f8
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$tmp_root/target
export CARGO_TERM_COLOR=never
export LC_ALL=C

test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected"
/usr/bin/mkdir -p "$tmp_root/source"
/usr/bin/tar -xzf "$archive" -C "$tmp_root/source"
test -f "$tmp_root/source/km-adaptive-comp-v2/engine/Cargo.toml"
cd "$tmp_root/source/km-adaptive-comp-v2/engine"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16

binary=$CARGO_TARGET_DIR/release/km
"$binary" routes >/dev/null
/usr/bin/install -m 0555 "$binary" "$root/km"
/usr/bin/sha256sum "$root/km"
echo "ADAPTIVE_COMP_V2_BUILD_COMPLETE job=$SLURM_JOB_ID source_sha256=$expected"
