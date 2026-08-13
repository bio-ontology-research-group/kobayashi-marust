#!/bin/bash
#SBATCH --job-name=km-fd30da7-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-fd30da7-identity-elcert-20260813/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-fd30da7-identity-elcert-20260813
archive=$root/source-fd30da7.tar.gz
expected_archive=$(cat "$root/source.sha256")
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected_archive" ]]
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
echo "BUILD_COMPLETE archive_sha256=$expected_archive binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
