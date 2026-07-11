#!/bin/bash
#SBATCH --job-name=km-kpset-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=16G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_disj_ext_auto_20260710/build-%j.out

set -euo pipefail

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_disj_ext_auto_20260710"
export CARGO_TARGET_DIR="$OUT/target"
export RUSTFLAGS=-Awarnings

cd "$ROOT/engine"
cargo build --release --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$OUT/km"
sha256sum "$OUT/km" > "$OUT/km.sha256"
cat "$OUT/km.sha256"
