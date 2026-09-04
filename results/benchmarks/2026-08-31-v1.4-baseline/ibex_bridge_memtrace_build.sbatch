#!/bin/bash
#SBATCH --job-name=km-v14-memtrace-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-bridge-memtrace-20260901/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-bridge-memtrace-20260901
archive=$root/source.tar.gz
expected=f6ff45b3620d941e511ff0a65107311148545eff900eb7430c4f377ba559e526
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
src=$root/source-$SLURM_JOB_ID
mkdir "$src"
tar -xzf "$archive" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export CARGO_TERM_COLOR=never
cd "$src/engine"
nice -n 5 cargo build --release --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km-ibex"
sha256sum "$root/km-ibex" > "$root/km-ibex.sha256"
"$root/km-ibex" routes >/dev/null
echo "BUILD_COMPLETE archive_sha256=$expected binary_sha256=$(cut -d' ' -f1 < "$root/km-ibex.sha256")"
