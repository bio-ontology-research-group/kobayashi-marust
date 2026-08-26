#!/bin/bash
#SBATCH --job-name=km-abox-elision-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=1
#SBATCH --mem=16G
#SBATCH --time=00:30:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-abox-elision-v7-20260825/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-abox-elision-v7-20260825
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR="$root/target"
export CARGO_TERM_COLOR=never
cd "$root/source/engine"
nice -n 5 cargo test --locked --lib separable_abox_elision_tests --jobs 1
nice -n 5 cargo build --release --locked --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km.native.tmp"
"$root/km.native.tmp" routes >/dev/null
mv "$root/km.native.tmp" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
echo "BUILD_COMPLETE binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
