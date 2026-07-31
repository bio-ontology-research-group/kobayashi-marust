#!/bin/bash
# Exact-signature gate for automatic component-ABox routing.
# Submit as --array=0-4 after staging the immutable binary and harness.
#SBATCH --job-name=km-7499-component
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/7499-component-abox-v1/gate-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/7499-component-abox-v1
km_root=/ibex/scratch/hohndor/km
expected_binary=1dda6ea210ee1a876168048dc504d7b07b3512d4b9ededaa3a7bdca6f42e96c8
ontologies=(
  ore_ont_7499.owl
  ore_ont_10702.owl
  ore_ont_15846.owl
  ore_ont_4755.owl
  ore_ont_6999.owl
)
ontology=${ontologies[$SLURM_ARRAY_TASK_ID]}

cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
if [[ $cpu_model != *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]; then
  echo "UNEXPECTED_CPU_MODEL model=[$cpu_model]" >&2
  exit 2
fi
cd "$root"
/usr/bin/sha256sum -c SHA256SUMS
test "$(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1)" = "$expected_binary"
test -s "$km_root/corpus/$ontology"
test -s "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz"

work=${SLURM_TMPDIR:-/tmp}/km-7499-component-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}
/usr/bin/mkdir -p "$work/run" "$root/results" "$root/failures"
/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_7499_component_gate \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --binary-sha "$expected_binary" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/failures" \
  --checkpoint "$root/results/$ontology.ibex.checkpoint.json" \
  > "$root/results/$ontology.ibex.json.tmp"

/usr/bin/python3 - "$root/results/$ontology.ibex.json.tmp" "$ontology" <<'PY'
import json
import sys
row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or not row.get("checkpointed"):
    raise SystemExit(f"provenance/checkpoint failure: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"exact gate failed: {row}")
PY
/usr/bin/mv "$root/results/$ontology.ibex.json.tmp" "$root/results/$ontology.ibex.json"
echo "TASK_COMPLETE ontology=$ontology"
