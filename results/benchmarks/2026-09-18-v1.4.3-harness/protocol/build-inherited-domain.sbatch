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
sha256sum -c candidate-inherited-domain.sha256
mkdir candidate-inherited-domain-source
tar -xzf candidate-inherited-domain.tar.gz -C candidate-inherited-domain-source
export CARGO_TARGET_DIR="$root/candidate-functional-data-target" CARGO_BUILD_JOBS=4
cargo build --release --locked --manifest-path "$root/candidate-inherited-domain-source/engine/Cargo.toml" --bin km
install -m 555 "$CARGO_TARGET_DIR/release/km" "$root/km-candidate-inherited-domain"
sha256sum "$root/km-candidate-inherited-domain" > "$root/km-candidate-inherited-domain.sha256"
