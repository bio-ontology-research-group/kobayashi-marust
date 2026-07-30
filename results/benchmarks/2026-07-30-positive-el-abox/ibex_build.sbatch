#!/bin/bash
# Build the source-bound candidate on an IBEX compute node for IBEX's glibc.
#SBATCH --job-name=km-elabox-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/positive-el-abox-20260730/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/positive-el-abox-20260730
tmp_root=${SLURM_TMPDIR:-$root}/build-$SLURM_JOB_ID
archive=$root/km-positive-el-abox-source.tar.gz
expected=05dccc44ba15f52ed7cefd9a56d35c894b289c8146015ac3961ec25eefd4432a
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$tmp_root/target
export CARGO_TERM_COLOR=never
export LC_ALL=C

test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected"
/usr/bin/mkdir -p "$tmp_root/source"
/usr/bin/tar -xzf "$archive" -C "$tmp_root/source"
cd "$tmp_root/source/engine"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16

binary=$CARGO_TARGET_DIR/release/km
"$binary" routes >/dev/null
/usr/bin/install -m 0555 "$binary" "$root/km"
/usr/bin/sha256sum "$root/km"
echo "EL_ABOX_BUILD_COMPLETE job=$SLURM_JOB_ID source_sha256=$expected"
