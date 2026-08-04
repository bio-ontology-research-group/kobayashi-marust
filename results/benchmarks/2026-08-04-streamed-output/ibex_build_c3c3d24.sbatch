#!/bin/bash
#SBATCH --job-name=km-c3c3d24-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --output=/ibex/scratch/hohndor/km/release-c3c3d24-auto-20260804/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/release-c3c3d24-auto-20260804
archive="$root/km-c3c3d24.tar.gz"
expected=b01764d009aac6301a108a2e175438e87a00f8528a314fedde2c72dae3e6ebed
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
echo "BUILD_COMPLETE revision=c3c3d24 job=$SLURM_JOB_ID"
