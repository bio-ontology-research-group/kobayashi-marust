#!/bin/bash
#SBATCH --job-name=km-02e6200-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/release-02e6200-auto-20260805/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/release-02e6200-auto-20260805
archive=$root/km-02e6200.tar.gz
expected=9bc2540caf545fbb8bc68f980475835ef164aba637d4b425c5f5b911c56e2e90
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
echo "BUILD_COMPLETE revision=02e6200 archive_sha256=$expected binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
