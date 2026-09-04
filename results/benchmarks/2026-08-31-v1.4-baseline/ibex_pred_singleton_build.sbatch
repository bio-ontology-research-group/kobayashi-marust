#!/bin/bash
#SBATCH --job-name=km-v14-par-pred-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-par-pred-20260901/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-par-pred-20260901
archive=$root/source.tar.gz
expected=c444a2822ae359c3224b6d239942818304fa03b70a4eed05961863692e3bb536
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
src=$root/source-$SLURM_JOB_ID
mkdir "$src"
tar -xzf "$archive" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export CARGO_TERM_COLOR=never
cd "$src/engine"
nice -n 5 cargo build --release --locked --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
"$root/km" routes >/dev/null
echo "BUILD_COMPLETE archive_sha256=$expected binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
