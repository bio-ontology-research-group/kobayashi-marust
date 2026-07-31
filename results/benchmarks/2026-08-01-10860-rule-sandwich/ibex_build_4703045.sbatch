#!/bin/bash
#SBATCH --job-name=km-4703045-build1
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=03:00:00
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/rule-clash-4703045/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715/rule-clash-4703045
archive="$root/source-4703045.tar.gz"
expected=074e60cbbab79c3fa2a6b3bcc53a9253fc7ffe63f6bfdd0f7388a666f4369290
test "$(sha256sum "$archive" | cut -d' ' -f1)" = "$expected"

src="$root/source-$SLURM_JOB_ID"
mkdir "$src"
tar -xzf "$archive" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR="${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID"
export CARGO_TERM_COLOR=never
cd "$src/engine"
nice -n 5 cargo build --release --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km"
"$root/km" routes >/dev/null
sha256sum "$root/km"
echo "BUILD_COMPLETE revision=4703045 job=$SLURM_JOB_ID"
