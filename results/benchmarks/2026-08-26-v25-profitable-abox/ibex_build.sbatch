#!/usr/bin/env bash
#SBATCH --job-name=km-v25-abox-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v25-profitable-abox-20260826/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v25-profitable-abox-20260826
archive=$root/source/v25-source-20260826.tar.gz
expected_archive_sha=14336b0cc3d7903d9975672c14df64357924131007650ceb729425ace532192a
[[ $(sha256sum "$archive" | awk '{print $1}') == "$expected_archive_sha" ]]
mkdir -p "$root/build/source"
tar -xzf "$archive" -C "$root/build/source"
export CARGO_TARGET_DIR=$root/target CARGO_BUILD_JOBS=4
cd "$root/build/source/engine"
cargo build --release --locked --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" | tee "$root/km.sha256"
"$root/km" routes >/dev/null
echo BUILD_COMPLETE
