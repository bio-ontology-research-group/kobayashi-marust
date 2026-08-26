#!/bin/bash
#SBATCH --job-name=km-simple-hierarchy-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=16G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-simple-hierarchy-20260825/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-simple-hierarchy-20260825
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR="$root/target"
export CARGO_TERM_COLOR=never
cd "$root/source/engine"
nice -n 5 cargo build --release --locked --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km.native.tmp"
"$root/km.native.tmp" routes >/dev/null
mv "$root/km.native.tmp" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
echo "BUILD_COMPLETE binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
