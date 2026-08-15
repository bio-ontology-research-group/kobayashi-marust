#!/bin/bash
#SBATCH --job-name=km-3215-labeltags-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/3215-label-tags-20260815/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/3215-label-tags-20260815
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/3215-reset-profile-20260814/target-50506024
export CARGO_TERM_COLOR=never
cd "$root/source/engine"
nice -n 5 cargo build --release --locked --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km.tmp"
"$root/km.tmp" routes >/dev/null
mv "$root/km.tmp" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
echo "BUILD_COMPLETE binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
