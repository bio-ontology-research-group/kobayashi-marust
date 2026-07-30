#!/bin/bash
# Build the giant-flat-taxonomy router from exact committed source.
#SBATCH --job-name=km-adaptive-comp-v6-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v6-20260731/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v6-20260731
tmp_root=${SLURM_TMPDIR:-$root}/build-$SLURM_JOB_ID
archive=$root/km-adaptive-comp-v6-2faf2ce.tar.gz
expected=1876fc4f4eef6d5999c590faccd7445c83acb635bf79e6679385b5a7e9814d27
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$tmp_root/target
export CARGO_TERM_COLOR=never
export LC_ALL=C

test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected"
/usr/bin/mkdir -p "$tmp_root/source"
/usr/bin/tar -xzf "$archive" -C "$tmp_root/source"
cd "$tmp_root/source/km-adaptive-comp-v6/engine"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16
binary=$CARGO_TARGET_DIR/release/km
"$binary" routes >/dev/null
/usr/bin/install -m 0555 "$binary" "$root/km"
/usr/bin/sha256sum "$root/km"
echo "ADAPTIVE_COMP_V6_BUILD_COMPLETE job=$SLURM_JOB_ID source_sha256=$expected"
