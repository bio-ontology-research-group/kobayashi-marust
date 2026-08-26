#!/usr/bin/env bash
#SBATCH --job-name=km-v27-mixed-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v27-mixed-profitability-20260826/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v27-mixed-profitability-20260826
archive=$root/source/v27-source-20260826.tar.gz
[[ $(sha256sum "$archive" | awk '{print $1}') == c41ce9ba2658c7f9a12983db15063402ef82bdc5be400143b21663afba1de43b ]]
mkdir -p "$root/build/source"
tar -xzf "$archive" -C "$root/build/source"
export CARGO_TARGET_DIR=$root/target CARGO_BUILD_JOBS=4
cd "$root/build/source/engine"
cargo build --release --locked --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" | tee "$root/km.sha256"
"$root/km" routes >/dev/null
echo BUILD_COMPLETE
