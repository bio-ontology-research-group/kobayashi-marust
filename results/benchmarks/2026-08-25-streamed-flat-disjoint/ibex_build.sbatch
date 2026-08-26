#!/bin/bash
#SBATCH --job-name=km-stream-flat-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-stream-flat-20260825/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-stream-flat-20260825
source_root=/ibex/user/hohndor/km/v110-stream-flat-20260825/source
tmp=${SLURM_TMPDIR:-/tmp/km-stream-flat-build-${SLURM_JOB_ID}}
rm -rf "$tmp"
mkdir -p "$tmp" "$root"
trap 'rm -rf "$tmp"' EXIT
export CARGO_BUILD_JOBS=8
export CARGO_TARGET_DIR="$tmp/target"
find "$source_root" -type f -print0 | sort -z | xargs -0 sha256sum > "$root/source-files.sha256"
sha256sum "$root/source-files.sha256" | tee "$root/source-manifest.sha256"
cd "$source_root/engine"
cargo test --release orchestrate::flat_nf1::tests
cargo test --release reachability_graph_json_matches_materialized_closure
cargo build --release --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" | tee "$root/km.sha256"
echo BUILD_COMPLETE
