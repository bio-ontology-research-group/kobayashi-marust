#!/usr/bin/env bash
#SBATCH --job-name=km-v16-mirror-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v16-mirror-query-split-20260826/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v16-mirror-query-split-20260826
archive=$root/source/v16-source-20260826.tar.gz
source_sha=065ca1e9aa85e0786b0ddb36614686c97455da6bf035b03b7b05474b4665ecc0
[[ $(sha256sum "$archive" | awk '{print $1}') == "$source_sha" ]]
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
