#!/usr/bin/env bash
#SBATCH --job-name=km-v13-flat-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826
archive=$root/source/v13-source-20260826.tar.gz
source_sha=7c41c73e9047124ac9d3ddd3b92593702a084618b5515ee721cc57ce90721172
[[ $(sha256sum "$archive" | awk '{print $1}') == "$source_sha" ]]
rm -rf "$root/build/source"
mkdir -p "$root/build/source"
tar -xzf "$archive" -C "$root/build/source"
export CARGO_TARGET_DIR=$root/target
export CARGO_BUILD_JOBS=4
cd "$root/build/source/engine"
cargo build --release --locked --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" | tee "$root/km.sha256"
"$root/km" routes >/dev/null
echo BUILD_COMPLETE
