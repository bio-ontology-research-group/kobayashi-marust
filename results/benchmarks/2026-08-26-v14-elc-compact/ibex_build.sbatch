#!/usr/bin/env bash
#SBATCH --job-name=km-v14-elc-compact-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-elc-compact-20260826/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v14-elc-compact-20260826
archive=$root/source/v14-source-20260826.tar.gz
source_sha=94931a31ad334beff27c315bb4512a236dd3cb844745de5c33032a4d967a5cf8
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
