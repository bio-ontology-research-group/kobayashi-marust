#!/bin/bash
#SBATCH --job-name=km-6600efe-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --output=/ibex/scratch/hohndor/km/release-6600efe-auto-20260804/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/release-6600efe-auto-20260804
archive="$root/km-6600efe.tar.gz"
expected=aefde41c675d7b1d9159fdb19db56f34152ea423cfa2a4410192abed749007ef
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
echo "BUILD_COMPLETE revision=6600efe job=$SLURM_JOB_ID"
