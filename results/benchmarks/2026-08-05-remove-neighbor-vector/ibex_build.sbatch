#!/bin/bash
#SBATCH --job-name=km-no-neighbor-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/remove-neighbor-vector-20260805/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/remove-neighbor-vector-20260805
archive=$root/source.tar.gz
expected=645b34c9afa256983fd900cdf76c7b08f96002a17758acd76d6f1c198f116fc1
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
src=$root/source-$SLURM_JOB_ID
mkdir "$src"
tar -xzf "$archive" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export CARGO_TERM_COLOR=never
cd "$src/engine"
nice -n 5 cargo build --release --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
"$root/km" routes >/dev/null
echo "BUILD_COMPLETE revision=4275690 archive_sha256=$expected binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
