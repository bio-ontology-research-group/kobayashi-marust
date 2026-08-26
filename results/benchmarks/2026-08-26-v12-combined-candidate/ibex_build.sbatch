#!/usr/bin/env bash
#SBATCH --job-name=km-v12-candidate-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v12-combined-candidate-20260826/build-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v12-combined-candidate-20260826
archive=$root/source/v12-source-20260826.tar.gz
source_sha=75c65d42b35677f01c2a09a9fe99efb421795b7fcda0d4db22d23d96a23c6670
build=$root/build

[[ $(sha256sum "$archive" | awk '{print $1}') == "$source_sha" ]]
rm -rf "$build/source"
mkdir -p "$build/source"
tar -xzf "$archive" -C "$build/source"
export CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v110-abox-elision-v7-20260825/target
export CARGO_BUILD_JOBS=4
cd "$build/source/engine"
cargo build --release --locked --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km-candidate"
sha256sum "$root/km-candidate" | tee "$root/km-candidate.sha256"
"$root/km-candidate" routes >/dev/null
echo BUILD_COMPLETE
