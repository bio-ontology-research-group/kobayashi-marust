#!/bin/bash
# Build the exact committed source on an IBEX compute node so the executable
# targets IBEX's glibc. The workstation binary is intentionally not deployed.
#SBATCH --job-name=km-int7499-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/integrated-build-20260730/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/integrated-build-20260730
focused=/ibex/scratch/hohndor/km/integrated-7499-20260730
full=/ibex/scratch/hohndor/km/integrated-main-full-20260730
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TERM_COLOR=never
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export LC_ALL=C

test "$(/usr/bin/cat "$root/revision.txt")" = "51502e3"
cd "$root/source/engine"
/usr/bin/nice -n 5 cargo build --release --bin km --jobs 32

binary=$CARGO_TARGET_DIR/release/km
"$binary" --help >/dev/null
install -m 0755 "$binary" "$focused/km"
install -m 0755 "$binary" "$full/km"
sha256sum "$focused/km" "$full/km"
cmp "$focused/km" "$full/km"
echo "INTEGRATED_BUILD_COMPLETE revision=51502e3 job=$SLURM_JOB_ID"
