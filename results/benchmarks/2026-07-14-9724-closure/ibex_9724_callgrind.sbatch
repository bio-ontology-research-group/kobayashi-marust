#!/bin/bash
#SBATCH --job-name=km-9724-callgrind
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=12G
#SBATCH --output=/ibex/scratch/hohndor/km/9724_closure_20260714/slurm/callgrind-%j.out

set -euo pipefail

module load valgrind/3.20.0/gnu-12.2.0

km_root=/ibex/scratch/hohndor/km
root=$km_root/9724_closure_20260714
binary=$root/km-9724-slow-debug
tin=$root/standalone/9724.tin.json
run=$root/callgrind
mkdir -p "$run" "$root/slurm"
/usr/bin/rm -f "$run"/callgrind.out.* "$run"/inclusive.txt "$run"/self.txt

echo "BEGIN host=$(hostname) date=$(date -Is) binary_sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)"

export KM_HT=1
export KM_HT_BRIDGE=1
export KM_HT_BRIDGE_ONLY=1
export KM_HT_FORCE=1
export KM_HT_CARD=1
export KM_HT_PAR=1
export KM_HT_QO_SHIQ=1
export KM_HT_BLOCK=5
export KM_HT_EAGER=1
export KM_HT_NEGTRIED=1
export KM_HT_ORD=1
export KM_HT_INCRBLOCK2=1
export KM_HT_INCROBLIG=1
export KM_TRIGGER_ABSORB=1
export KM_KEEP_CHAIN_AXIOMS=1
export KM_HT_SATURATION=1
export KM_HT_SATCACHE=1
export KM_HT_SATURATION_BUDGET_S=30
export KM_BRIDGE_PROBE_BUDGET_S=1
export KM_BRIDGE_RETRY_ROUNDS=0

set +e
/usr/bin/timeout -k 10 600 \
  valgrind \
    --tool=callgrind \
    --callgrind-out-file="$run/callgrind.out.%p" \
    --collect-atstart=yes \
    --dump-instr=yes \
    --collect-jumps=yes \
  "$binary" tableau \
    < "$tin" \
    > "$run/9724.json" \
    2> "$run/9724.stderr"
status=$?
set -e

profile=$(/usr/bin/find "$run" -maxdepth 1 -name 'callgrind.out.*' -type f | /usr/bin/sort | /usr/bin/tail -n 1)
echo "RESULT exit=$status profile=$profile bytes=$(/usr/bin/stat -c %s "$profile")"
callgrind_annotate --inclusive=yes --threshold=0.25 "$profile" > "$run/inclusive.txt"
callgrind_annotate --inclusive=no --threshold=0.25 "$profile" > "$run/self.txt"
/usr/bin/sed -n '1,180p' "$run/self.txt"
echo "END date=$(date -Is)"
