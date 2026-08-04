#!/bin/bash
#SBATCH --job-name=km-2dc5e52-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/json-iri-intern-20260804/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/json-iri-intern-20260804
archive=$root/km-2dc5e52.tar.gz
expected=5ff27bccde1c6221a2ede987602e99c4fcb6e00e9697f02685ffcb951f1ebf00
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
echo "BUILD_COMPLETE revision=2dc5e52 archive_sha256=$expected binary_sha256=$(cut -d' ' -f1 < "$root/km-candidate.sha256")"
