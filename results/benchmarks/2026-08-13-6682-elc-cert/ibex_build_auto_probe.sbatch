#!/bin/bash
#SBATCH --job-name=km-6682-probe-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
archive=$root/km-6682-auto-probe-v2.tar.gz
expected=8528081662d3dd2cc34df8d865b228c8c265c0ce8258ea9ca6aac6c0179bc9c6
[[ $(sha256sum "$archive" | cut -d" " -f1) == "$expected" ]]
src=$root/source-$SLURM_JOB_ID
mkdir "$src"
tar -xzf "$archive" -C "$src" --strip-components=1
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
