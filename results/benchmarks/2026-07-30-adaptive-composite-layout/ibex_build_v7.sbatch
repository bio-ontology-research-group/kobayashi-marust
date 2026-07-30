#!/bin/bash
# Build the bottom-aware giant-flat-taxonomy router from committed source.
#SBATCH --job-name=km-adaptive-comp-v7-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731
tmp_root=${SLURM_TMPDIR:-$root}/build-$SLURM_JOB_ID
archive=$root/km-adaptive-comp-v7-ae898de.tar.gz
expected=96d94aaf227388b17415f1474e6f8383176e2df1af386fdde1d8df9933ec16a7
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$tmp_root/target
export CARGO_TERM_COLOR=never
export LC_ALL=C

test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected"
/usr/bin/mkdir -p "$tmp_root/source"
/usr/bin/tar -xzf "$archive" -C "$tmp_root/source"
cd "$tmp_root/source/km-adaptive-comp-v7/engine"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16
binary=$CARGO_TARGET_DIR/release/km
"$binary" routes >/dev/null
/usr/bin/install -m 0555 "$binary" "$root/km"
/usr/bin/sha256sum "$root/km"
echo "ADAPTIVE_COMP_V7_BUILD_COMPLETE job=$SLURM_JOB_ID source_sha256=$expected"
