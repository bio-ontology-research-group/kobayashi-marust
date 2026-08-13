#!/bin/bash
#SBATCH --job-name=km-build-ofn-borrowed
#SBATCH --partition=debug
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --time=01:00:00
#SBATCH --output=/ibex/scratch/hohndor/km/frontend-borrowed-names-20260813/build-final-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/frontend-borrowed-names-20260813
export CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v0215-next-profile/target
cd "$root/source"
cargo build --release --bin km
cp "$CARGO_TARGET_DIR/release/km" "$root/km-final"
sha256sum "$root/km-final"
