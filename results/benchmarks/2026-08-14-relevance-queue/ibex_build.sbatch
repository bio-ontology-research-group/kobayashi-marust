#!/bin/bash
#SBATCH --job-name=km-build-relevance-queue
#SBATCH --partition=debug
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --time=01:00:00
#SBATCH --output=/ibex/scratch/hohndor/km/relevance-queue-20260813/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/relevance-queue-20260813
export CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v0215-next-profile/target
cd "$root/source"
cargo build --release --bin km
cp "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km"
