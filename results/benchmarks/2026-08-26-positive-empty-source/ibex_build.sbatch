#!/bin/bash
#SBATCH --job-name=km-v110-v7-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v7-20260826/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v7-20260826
archive=$root/source/v7-source-20260826.tar.gz
expected_source=1a715e82fad239b96a005c84e696e0b32de8d1b7c7e0ba0d84378ffeef6e9a16
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected_source" ]]
export CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v110-abox-elision-v7-20260825/target
export CARGO_BUILD_JOBS=4
cd "$root/source/engine"
cargo build --release --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" | tee "$root/km.sha256"
echo BUILD_COMPLETE
