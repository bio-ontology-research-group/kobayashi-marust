#!/bin/bash
# Build the exact committed source on an IBEX compute node.
# The source archive and resulting executable are hash-bound.
#SBATCH --job-name=km-9635-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/datatype-bridge-9635-20260730/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/datatype-bridge-9635-20260730
tmp_root=${SLURM_TMPDIR:-$root}/build-$SLURM_JOB_ID
archive=$root/km-9635-93dcec4.tar.gz
expected=39850e9eca2359b87ebc88d468ddc3c7f8eb6215628d210ce5fad2b781ddcb83
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$tmp_root/target
export CARGO_TERM_COLOR=never
export LC_ALL=C

test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected"
/usr/bin/mkdir -p "$tmp_root/source"
/usr/bin/tar -xzf "$archive" -C "$tmp_root/source"
test -f "$tmp_root/source/km-9635/engine/Cargo.toml"
cd "$tmp_root/source/km-9635/engine"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16

binary=$CARGO_TARGET_DIR/release/km
"$binary" routes >/dev/null
/usr/bin/install -m 0555 "$binary" "$root/km"
/usr/bin/sha256sum "$root/km"
echo "DATATYPE_BRIDGE_BUILD_COMPLETE job=$SLURM_JOB_ID source_sha256=$expected"
