#!/bin/bash
#SBATCH --job-name=km-v110-v11-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826
archive=$root/source/v11-source-20260826.tar.gz
expected_source=02f38c0f33ff5dee64f258ba6739394d7c3478da30bad99a6d94c569137d4d29
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected_source" ]]
export CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v110-abox-elision-v7-20260825/target
export CARGO_BUILD_JOBS=4
cd "$root/source/engine"
cargo build --release --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" | tee "$root/km.sha256"
echo BUILD_COMPLETE
