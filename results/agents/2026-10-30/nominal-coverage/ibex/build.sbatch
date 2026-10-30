#!/bin/bash
#SBATCH --job-name=km155-nc-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=03:00:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v155-nominal-coverage-20261030/slurm/build-%j.out
set -euo pipefail
ROOT=/ibex/scratch/projects/c2014/hohndor/km/v155-nominal-coverage-20261030
TAG=${KM_TAG:?}
build=${SLURM_TMPDIR:-$ROOT/tmp}/km155nc-build-$TAG
/usr/bin/rm -rf "$build"; /usr/bin/mkdir -p "$build/src"
/usr/bin/tar -xzf "$ROOT/src-$TAG.tar.gz" -C "$build/src"
cd "$build/src/engine"
CARGO_TARGET_DIR="$build/target" nice cargo build --release --bin km
/usr/bin/install -m 755 "$build/target/release/km" "$ROOT/km-$TAG"
/usr/bin/sha256sum "$ROOT/km-$TAG" > "$ROOT/km-$TAG.sha256"
/usr/bin/rm -rf "$build"
echo "BUILD_OK $TAG $(/usr/bin/hostname)"
