#!/bin/bash
# Build the source-bound positive-component-ABox candidate on IBEX compute.
#SBATCH --job-name=km-7499-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/7499-component-abox-v1/build-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/7499-component-abox-v1
archive=$root/source-616521a.tar.gz
expected_source=09e1810d492de1bada92dd6b8c14c4ef68c9b82b628b05c821ec504ed3441b1d
test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected_source"

work=${SLURM_TMPDIR:-/tmp}/km-7499-build-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work/source" "$work/target"
/usr/bin/tar -xzf "$archive" -C "$work/source"
cd "$work/source/engine"
export CARGO_TARGET_DIR="$work/target"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16
/usr/bin/install -m 755 "$work/target/release/km" "$root/km-cluster"
/usr/bin/sha256sum "$root/km-cluster" > "$root/km-cluster.sha256"
"$root/km-cluster" profile /ibex/scratch/hohndor/km/corpus/ore_ont_7499.owl \
  > "$root/source-smoke.profile.json"
echo "BUILD_COMPLETE source=$expected_source binary=$(/usr/bin/cut -d' ' -f1 "$root/km-cluster.sha256")"
