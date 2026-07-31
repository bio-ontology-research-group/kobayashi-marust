#!/bin/bash
# Build the focused-probe binary on IBEX so its libc baseline matches compute nodes.
#SBATCH --job-name=km-10702-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/10702-ni-cert-v1/build-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/10702-ni-cert-v1
work=${SLURM_TMPDIR:-/tmp}/km-10702-build-${SLURM_JOB_ID}
test -s "$root/source.tar.gz"
/usr/bin/mkdir -p "$work/source" "$work/target"
/usr/bin/tar -xzf "$root/source.tar.gz" -C "$work/source"

cd "$work/source/engine"
CARGO_TARGET_DIR="$work/target" /usr/bin/env cargo build --release --bin km
/usr/bin/install -m 755 "$work/target/release/km" "$root/km.ibex.tmp"
/usr/bin/sha256sum "$root/km.ibex.tmp" > "$root/km.ibex.sha256.tmp"
/usr/bin/mv "$root/km.ibex.tmp" "$root/km.ibex"
/usr/bin/mv "$root/km.ibex.sha256.tmp" "$root/km.ibex.sha256"
test -x "$root/km.ibex"
echo "BUILD_COMPLETE"
