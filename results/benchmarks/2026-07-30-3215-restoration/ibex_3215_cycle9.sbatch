#!/bin/bash
# Build the cycle9 KM source on IBEX and measure ore_ont_3215 under the
# benchmark contract (240 s wall, 20 GiB peak) on an exclusive Gold 6248 node.
#SBATCH --job-name=km-cycle9-3215
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/cycle9-3215-src/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/cycle9-3215-src
km_root=/ibex/scratch/hohndor/km
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TERM_COLOR=never
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export LC_ALL=C

cd "$root/engine"
/usr/bin/nice -n 5 cargo build --release --bin km --jobs 32
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km-cycle9"
sha256sum "$root/km-cycle9"

ont=$km_root/corpus/ore_ont_3215.owl
gold=$km_root/gold/konclude__ore_ont_3215.owl.sig.gz
out=$root/run-$SLURM_JOB_ID
mkdir -p "$out"

run_arm() {
  local name=$1; shift
  echo "=== ARM $name ==="
  set +e
  env "$@" KM_THREADS=16 /usr/bin/time -v timeout 240 \
    "$root/km-cycle9" classify "$ont" > "$out/$name.json" 2> "$out/$name.time"
  local rc=$?
  set -e
  echo "rc=$rc"
  /usr/bin/grep -E "Elapsed \(wall|Maximum resident" "$out/$name.time" || true
  if [ $rc -eq 0 ]; then
    /usr/bin/python3 "$root/kmsig.py" "$out/$name.json" "$gold"
  else
    echo "ARM $name did not finish inside 240 s"
  fi
}

run_arm bridge KM_ROUTE=ht_bridge
run_arm auto KM_ROUTE=auto

echo "CYCLE9_3215_COMPLETE job=$SLURM_JOB_ID"
