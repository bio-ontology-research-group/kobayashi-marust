#!/bin/bash
#SBATCH --job-name=km-build-or-debug
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=16G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/build-or-debug-%j.out

set -euo pipefail
ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711/km-or-debug"
export CARGO_TARGET_DIR="$ROOT/engine/target"
export RUSTFLAGS=-Awarnings

cd "$ROOT/engine"
cargo build --release --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$OUT"
sha256sum "$OUT"
