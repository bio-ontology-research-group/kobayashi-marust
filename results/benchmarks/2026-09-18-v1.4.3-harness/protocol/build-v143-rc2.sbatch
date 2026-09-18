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
sha256sum -c candidate-v143-rc2.sha256
mkdir candidate-v143-rc2-source
tar -xzf candidate-v143-rc2.tar.gz -C candidate-v143-rc2-source
export CARGO_TARGET_DIR="$root/candidate-reporting-cpu-target" CARGO_BUILD_JOBS=4
cargo build --release --locked --manifest-path "$root/candidate-v143-rc2-source/engine/Cargo.toml" --bin km
install -m 555 "$CARGO_TARGET_DIR/release/km" "$root/km-candidate-v143-rc2"
sha256sum "$root/km-candidate-v143-rc2" > "$root/km-candidate-v143-rc2.sha256"
