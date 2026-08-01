#!/bin/bash
#SBATCH --job-name=km-1f2f46b-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=03:00:00
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/guarded-role-1f2f46b/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715/guarded-role-1f2f46b
archive="$root/source-1f2f46b.tar.gz"
expected=cbdb06566ebf5c431e524b1ec47ab426f545d31f64c410288b00ef3434f889ea
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
echo "BUILD_COMPLETE revision=1f2f46b job=$SLURM_JOB_ID"
