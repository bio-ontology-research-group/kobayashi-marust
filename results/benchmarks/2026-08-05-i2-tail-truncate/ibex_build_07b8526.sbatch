#!/bin/bash
#SBATCH --job-name=km-07b8526-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/i2-tail-truncate-20260805/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/i2-tail-truncate-20260805
archive=$root/km-07b8526.tar.gz
expected=02f6eca1ebc7289dcd0fabe14a09fccd5a07be7d1901e89570b721cc5114b087
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
echo "BUILD_COMPLETE revision=07b8526 archive_sha256=$expected binary_sha256=$(cut -d' ' -f1 < "$root/km-candidate.sha256")"
