#!/bin/bash
#SBATCH --job-name=km-i2-mask-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=4
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/i2-incremental-mask-20260813/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/i2-incremental-mask-20260813
expected=$(cat "$root/source.sha256")
[[ $(sha256sum "$root/source.tar.gz" | cut -d' ' -f1) == "$expected" ]]
src=$root/source-$SLURM_JOB_ID; mkdir "$src"; tar -xzf "$root/source.tar.gz" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID CARGO_TERM_COLOR=never
cd "$src/engine"; nice -n 5 cargo build --release --locked --bin km --jobs 4
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km.tmp"; "$root/km.tmp" routes >/dev/null; mv "$root/km.tmp" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
echo "BUILD_COMPLETE archive_sha256=$expected binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
