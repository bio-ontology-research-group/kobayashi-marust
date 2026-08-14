#!/bin/bash
#SBATCH --job-name=km-build-elc-typed-input-route-drop
#SBATCH --partition=debug
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --time=01:00:00
#SBATCH --output=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814/build-elc-typed-input-route-drop-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/move-augment-right-sized-20260814
export CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v0215-next-profile/target
cd "$root/source-elc-typed-input-route-drop"
cargo build --release --bin km
cp "$CARGO_TARGET_DIR/release/km" "$root/km-elc-typed-input-route-drop"
sha256sum "$root/km-elc-typed-input-route-drop"
