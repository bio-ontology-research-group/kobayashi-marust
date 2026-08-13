#!/bin/bash
#SBATCH --job-name=km-2a32741-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-2a32741-el-bottom-20260805/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-2a32741-el-bottom-20260805
archive=$root/km-2a32741.tar.gz
expected=2e335345b7a6ea17edda2c13e1f91da9e767c359e7654b3ef902ea8b53c15bc8
[[ $(sha256sum "$archive" | cut -d" " -f1) == "$expected" ]]
src=$root/source-$SLURM_JOB_ID
mkdir "$src"
tar -xzf "$archive" -C "$src" --strip-components=1
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export CARGO_TERM_COLOR=never
cd "$src/engine"
nice -n 5 cargo build --release --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
"$root/km" routes >/dev/null
echo "BUILD_COMPLETE revision=2a32741 archive_sha256=$expected binary_sha256=$(cut -d" " -f1 < "$root/km.sha256")"
