#!/bin/bash
# Build the source-bound candidate against the IBEX compute-node glibc.
#SBATCH --job-name=km-6934-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/6934-ni-abox-v1/build-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/6934-ni-abox-v1
archive=$root/source-5cfccc5.tar.gz
expected_source=e7fbdfee4b6824e48035b9231f22da0e43d7975f42462120037ea29f19e9c49f
test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected_source"

work=${SLURM_TMPDIR:-/tmp}/km-6934-build-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work/source" "$work/target"
/usr/bin/tar -xzf "$archive" -C "$work/source"
cd "$work/source/engine"
export CARGO_TARGET_DIR="$work/target"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16
/usr/bin/install -m 755 "$work/target/release/km" "$root/km-cluster"
/usr/bin/sha256sum "$root/km-cluster" > "$root/km-cluster.sha256"
"$root/km-cluster" profile /ibex/scratch/hohndor/km/corpus/ore_ont_6999.owl \
  > "$root/source-smoke.profile.json"
echo "BUILD_COMPLETE source=$expected_source binary=$(/usr/bin/cut -d' ' -f1 "$root/km-cluster.sha256")"
