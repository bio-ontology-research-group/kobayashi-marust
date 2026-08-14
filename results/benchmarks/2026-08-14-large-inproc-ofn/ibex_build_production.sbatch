#!/bin/bash
#SBATCH --job-name=km-build-large-inproc-ofn-production
#SBATCH --partition=debug
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --time=01:00:00
#SBATCH --output=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814/build-production-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/large-inproc-ofn-20260814
export CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v0215-next-profile/target
cd "$root/source-production"
cargo build --release --bin km
cp "$CARGO_TARGET_DIR/release/km" "$root/km-production"
sha256sum "$root/km-production"
