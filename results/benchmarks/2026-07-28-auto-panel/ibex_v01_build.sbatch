#!/bin/bash
#SBATCH --job-name=km-v01-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=08:00:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/auto-v01-d2aa211/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/auto-v01-d2aa211
archive=$root/source.tar.gz
build=$root/build
revision=d2aa211
echo "d51d303632a2630b73f93457831dc42415527c6f2890efcbac66c62a5f00f679  $archive" | /usr/bin/sha256sum -c -
[[ ! -e $build ]] || { echo "refusing existing build root" >&2; exit 2; }
/usr/bin/mkdir -p "$build/source" "$build/bin" "$build/target"
/usr/bin/tar -xzf "$archive" -C "$build/source"
export CARGO_TARGET_DIR=$build/target
export RUSTFLAGS=-Ctarget-cpu=native
export CARGO_INCREMENTAL=0
cd "$build/source/engine"
/usr/bin/nice -n 5 /home/hohndor/.cargo/bin/cargo build --release --bin km
/usr/bin/install -m 0750 "$CARGO_TARGET_DIR/release/km" "$build/bin/km"
"$build/bin/km" routes >"$build/routes.txt"
/usr/bin/awk -F '\t' '$1=="auto"{a=1} $1=="auto-speed"{s=1} $1=="auto-memory"{m=1} END{exit !(a&&s&&m)}' "$build/routes.txt"
echo "V01_BUILD_COMPLETE revision=$revision"
