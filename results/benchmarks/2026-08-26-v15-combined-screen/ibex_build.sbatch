#!/usr/bin/env bash
#SBATCH --job-name=km-v15-screen-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v15-combined-screen-20260826/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v15-combined-screen-20260826
archive=$root/source/v15-source-20260826.tar.gz
source_sha=329b34defb6c55ab075f3776fc22de46b96a7ae4ecf9f479db494aa1ccd9c8cf
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
