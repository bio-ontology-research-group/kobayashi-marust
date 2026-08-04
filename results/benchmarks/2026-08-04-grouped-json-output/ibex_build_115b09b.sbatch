#!/bin/bash
#SBATCH --job-name=km-grouped-json-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/grouped-json-output-20260804/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/grouped-json-output-20260804
archive=$root/km-115b09b.tar.gz
expected=9302f5010bac0c63a87cfc7442183bfe1893fe4c8a12c6fa0d2e82700729b2ca
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
src=$root/source-$SLURM_JOB_ID
mkdir "$src"
tar -xzf "$archive" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export CARGO_TERM_COLOR=never
cd "$src/engine"
nice -n 5 cargo build --release --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km-candidate"
sha256sum "$root/km-candidate" > "$root/km-candidate.sha256"
"$root/km-candidate" routes >/dev/null
echo "BUILD_COMPLETE revision=115b09b archive_sha256=$expected binary_sha256=$(cut -d' ' -f1 < "$root/km-candidate.sha256")"
