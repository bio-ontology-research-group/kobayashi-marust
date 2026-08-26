#!/usr/bin/env bash
#SBATCH --job-name=km-v19-horn-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v19-sparse-horn-20260826/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v19-sparse-horn-20260826
archive=$root/source/v19-source-20260826.tar.gz
[[ $(sha256sum "$archive" | awk '{print $1}') == 41bcdcb85288d87b835a50257e8e2fc9d40d0a8b6125d093da5501ecf2f36de6 ]]
mkdir -p "$root/build/source"
tar -xzf "$archive" -C "$root/build/source"
export CARGO_TARGET_DIR=$root/target CARGO_BUILD_JOBS=4
cd "$root/build/source/engine"
cargo build --release --locked --bin km
install -m 755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" | tee "$root/km.sha256"
"$root/km" routes >/dev/null
echo BUILD_COMPLETE
