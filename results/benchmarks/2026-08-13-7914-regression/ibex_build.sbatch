#!/bin/bash
#SBATCH --job-name=km-7914-reg-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-2%3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/7914-regression-20260813/build-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/7914-regression-20260813
revs=(a639ab5 cff26d2-parent cff26d2)
rev=${revs[${SLURM_ARRAY_TASK_ID:?}]}
src="$root/source/$rev"
target="$root/target/$rev"
out="$root/bin/km-$rev"
test -f "$src/engine/Cargo.toml"
mkdir -p "$target" "$root/bin"
cd "$src/engine"
CARGO_TARGET_DIR="$target" cargo build --release --bin km
install -m 0555 "$target/release/km" "$out.tmp"
sha256sum "$out.tmp" > "$out.sha256.tmp"
mv "$out.tmp" "$out"
mv "$out.sha256.tmp" "$out.sha256"
echo BUILD_COMPLETE revision=$rev binary=$(sha256sum "$out" | cut -d' ' -f1)
