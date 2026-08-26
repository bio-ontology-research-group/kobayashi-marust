#!/bin/bash
#SBATCH --job-name=km-flat-nf1-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-direct-flat-source-20260825/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-direct-flat-source-20260825
export CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v110-abox-elision-v7-20260825/target
export CARGO_BUILD_JOBS=4
cd "$root/source/engine"
cargo test --release flat_nf1::tests -- --nocapture
cargo build --release --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" | tee "$root/km.sha256"
echo BUILD_COMPLETE
