#!/bin/bash
# Build the exact committed source on an IBEX compute node.
#SBATCH --job-name=km-1194-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/class-only-chain-abox-1194-20260730/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/class-only-chain-abox-1194-20260730
tmp_root=${SLURM_TMPDIR:-$root}/build-$SLURM_JOB_ID
archive=$root/km-1194-a513828.tar.gz
expected=3958bb7660abd7c090263b5dad2a2885664cc810e6b4e47f7232997bf98d1418
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$tmp_root/target
export CARGO_TERM_COLOR=never
export LC_ALL=C

test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected"
/usr/bin/mkdir -p "$tmp_root/source"
/usr/bin/tar -xzf "$archive" -C "$tmp_root/source"
test -f "$tmp_root/source/kobayashi-marust/engine/Cargo.toml"
cd "$tmp_root/source/kobayashi-marust/engine"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16

binary=$CARGO_TARGET_DIR/release/km
"$binary" routes >/dev/null
/usr/bin/install -m 0555 "$binary" "$root/km"
/usr/bin/sha256sum "$root/km"
echo "CLASS_ONLY_CHAIN_ABOX_BUILD_COMPLETE job=$SLURM_JOB_ID source_sha256=$expected"
