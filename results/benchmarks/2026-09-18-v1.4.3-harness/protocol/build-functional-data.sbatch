#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --time=00:40:00
#SBATCH --job-name=km-v143-candidate-build
set -euo pipefail
root=/ibex/scratch/hohndor/km/v143-harness-20260918
cd "$root"
sha256sum -c candidate-functional-data.sha256
mkdir candidate-functional-data-source
tar -xzf candidate-functional-data.tar.gz -C candidate-functional-data-source
export CARGO_TARGET_DIR="$root/candidate-functional-data-target" CARGO_BUILD_JOBS=4
cargo build --release --locked --manifest-path "$root/candidate-functional-data-source/engine/Cargo.toml" --bin km
install -m 555 "$CARGO_TARGET_DIR/release/km" "$root/km-candidate-functional-data"
sha256sum "$root/km-candidate-functional-data" > "$root/km-candidate-functional-data.sha256"
