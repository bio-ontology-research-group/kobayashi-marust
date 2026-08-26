#!/bin/bash
#SBATCH --job-name=km-builtin-flat-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-builtin-flat-20260825/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-builtin-flat-20260825
source_root=$root/source
tmp=${SLURM_TMPDIR:-/tmp}/km-builtin-flat-build-${SLURM_JOB_ID}
rm -rf "$tmp"
mkdir -p "$tmp" "$root"
trap 'rm -rf "$tmp"' EXIT
export CARGO_BUILD_JOBS=8
export CARGO_TARGET_DIR="$tmp/target"
find "$source_root" -type f -print0 | sort -z | xargs -0 sha256sum > "$root/source-files.sha256"
sha256sum "$root/source-files.sha256" | tee "$root/source-manifest.sha256"
cd "$source_root/engine"
cargo test --release --lib orchestrate::flat_nf1::tests
cargo test --release --lib reachability_graph_json
cargo test --release --lib orchestrate::mirror::tests
cd "$source_root/engine"
cargo build --release --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" | tee "$root/km.sha256"
echo BUILD_COMPLETE
