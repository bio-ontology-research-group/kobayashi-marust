#!/bin/bash
#SBATCH --job-name=kon-9724-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/9724_closure_20260714/slurm/konclude-build-%j.out

set -euo pipefail

module load qt/5.15.5/gnu-12.2.0

km_root=/ibex/scratch/hohndor/km
root=$km_root/9724_closure_20260714
base=$km_root/Konclude-debug
build=$root/Konclude-9724-debug-native
instrumentation=$root/konclude-9724-seed-instrumentation.patch
mkdir -p "$root/slurm"

echo "BEGIN host=$(hostname) date=$(date -Is)"
if [[ ! -d "$build" ]]; then
  /usr/bin/cp -a "$base" "$build"
fi
/usr/bin/cp \
  "$base/Source/Reasoner/Consistiser/CTotallyPrecomputationThread.cpp" \
  "$build/Source/Reasoner/Consistiser/CTotallyPrecomputationThread.cpp"
# The upstream file uses CRLF. Normalize only this copied build-tree source so
# the preserved text patch applies independently of checkout line endings.
/usr/bin/sed -i 's/\r$//' \
  "$build/Source/Reasoner/Consistiser/CTotallyPrecomputationThread.cpp"
/usr/bin/patch -d "$build" -p1 < "$instrumentation"
/usr/bin/touch \
  "$build/Source/Reasoner/Consistiser/CTotallyPrecomputationThread.cpp"

make -C "$build" -j16

/usr/bin/sha256sum "$build/Release/Konclude"
echo "END date=$(date -Is)"
