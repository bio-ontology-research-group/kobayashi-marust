#!/bin/bash
#SBATCH --job-name=km-v110-v10-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v10-20260826/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v10-20260826
archive=$root/source/v10-source-20260826.tar.gz
expected_source=d24f3e62267501bca4a1cb1a308ca9f705e5869b971d15b5fea4827d1c6980f5
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected_source" ]]
export CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v110-abox-elision-v7-20260825/target
export CARGO_BUILD_JOBS=4
cd "$root/source/engine"
cargo build --release --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" | tee "$root/km.sha256"
echo BUILD_COMPLETE
