#!/bin/bash
# Build the pre-clausification 9724 bridge router on IBEX.
# The output checksum is written beside the binary for the dependent gate.
#SBATCH --job-name=km-v12-9724-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v12-9724-gate-20260731/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v12-9724-gate-20260731
tmp_root=${SLURM_TMPDIR:-$root}/build-$SLURM_JOB_ID
archive=$root/km-f6b2188-source.tar.gz
expected_source=b8febb611fd088867960b07fca70e75a1c59ac6922026657f02be682de274239
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$tmp_root/target
export CARGO_TERM_COLOR=never
export LC_ALL=C

test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected_source"
/usr/bin/mkdir -p "$tmp_root/source"
/usr/bin/tar -xzf "$archive" -C "$tmp_root/source"
test -f "$tmp_root/source/engine/Cargo.toml"
cd "$tmp_root/source/engine"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16
binary=$CARGO_TARGET_DIR/release/km
"$binary" routes >/dev/null
/usr/bin/install -m 0555 "$binary" "$root/km.ibex.tmp"
/usr/bin/sha256sum "$root/km.ibex.tmp" | /usr/bin/cut -d' ' -f1 > "$root/km.sha256.tmp"
/usr/bin/mv "$root/km.ibex.tmp" "$root/km"
/usr/bin/mv "$root/km.sha256.tmp" "$root/km.sha256"
echo "KM_V12_9724_BUILD_COMPLETE job=$SLURM_JOB_ID source_sha256=$expected_source binary_sha256=$(cat "$root/km.sha256")"
