#!/bin/bash
#SBATCH --job-name=km-d607ca7-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-d607ca7-elcert-20260813/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-d607ca7-elcert-20260813
archive=$root/source-d607ca7.tar.gz
expected=efb5c6cd5698d5b46599f35d31ac7ac18fa14f0030bf63b48bf1f745bb1b8c10
[[ $(sha256sum "$archive" | cut -d" " -f1) == "$expected" ]]
src=$root/source-$SLURM_JOB_ID
mkdir "$src"
tar -xzf "$archive" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export CARGO_TERM_COLOR=never
cd "$src/engine"
nice -n 5 cargo build --release --locked --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km.ibex.tmp"
"$root/km.ibex.tmp" routes >/dev/null
mv "$root/km.ibex.tmp" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
echo "BUILD_COMPLETE archive_sha256=$expected binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
