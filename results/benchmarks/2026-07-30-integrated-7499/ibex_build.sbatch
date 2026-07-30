#!/bin/bash
# Build the exact committed source on an IBEX compute node so the executable
# targets IBEX's glibc. The workstation binary is intentionally not deployed.
#SBATCH --job-name=km-main4368-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/integrated-build-main-20260730/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/integrated-build-main-20260730
focused=/ibex/scratch/hohndor/km/integrated-7499-20260730
full=/ibex/scratch/hohndor/km/integrated-main-full-20260730
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TERM_COLOR=never
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export LC_ALL=C

archive=$root/km-main-4368e2e.tar.gz
test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = \
  "050a6c3e940f27f52eb30374bc622099bb0b4b7230010eeb43ebbd7344f8f22a"
/usr/bin/mkdir "$root/source-$SLURM_JOB_ID"
/usr/bin/tar -xzf "$archive" -C "$root/source-$SLURM_JOB_ID"
cd "$root/source-$SLURM_JOB_ID/engine"
/usr/bin/nice -n 5 cargo build --release --bin km --jobs 32

binary=$CARGO_TARGET_DIR/release/km
"$binary" routes >/dev/null
install -m 0755 "$binary" "$focused/km"
install -m 0755 "$binary" "$full/km"
sha256sum "$focused/km" "$full/km"
cmp "$focused/km" "$full/km"
echo "INTEGRATED_BUILD_COMPLETE revision=4368e2e job=$SLURM_JOB_ID"
