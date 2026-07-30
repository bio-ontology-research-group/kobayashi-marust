#!/bin/bash
# Regression panel with the repository canonicaliser: every documented
# bridge-closed terminology plus the KPSet-barrier correctness cases, on the
# production `auto` route under the benchmark contract (240 s, 20 GiB).
#SBATCH --job-name=km-cycle9-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/cycle9-3215-src/slurm-%x-%j.out

set -uo pipefail
root=/ibex/scratch/hohndor/km/cycle9-3215-src
km_root=/ibex/scratch/hohndor/km
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export LC_ALL=C PYTHONHASHSEED=0

out=$root/panel-$SLURM_JOB_ID
mkdir -p "$out"
bin=$root/km-cycle9
sha256sum "$bin"

for id in 148 541 3215 4054 4669 4755 7127 7581 7914 8068 8864 9540 9663 9724 \
          10621 11315 11745 12414 12653 14817; do
  ont=$km_root/corpus/ore_ont_$id.owl
  gold=$km_root/gold/konclude__ore_ont_$id.owl.sig.gz
  env KM_THREADS=16 /usr/bin/time -f "%e %M" -o "$out/$id.time" timeout 240 \
    "$bin" classify "$ont" > "$out/$id.json" 2> "$out/$id.err"
  rc=$?
  stats=$(/usr/bin/tail -1 "$out/$id.time" 2>/dev/null)
  if [ $rc -eq 0 ]; then
    verdict=$(/usr/bin/python3 "$root/kmsig.py" "$out/$id.json" "$gold" | /usr/bin/tr '\n' ' ')
    echo "PANEL ont=$id rc=$rc stats=[$stats] $verdict"
  else
    echo "PANEL ont=$id rc=$rc stats=[$stats] status=timeout-or-error"
  fi
  rm -f "$out/$id.json"
done

echo "CYCLE9_PANEL_COMPLETE job=$SLURM_JOB_ID"
