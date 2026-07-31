#!/bin/bash
# Source-bound exact-signature gate for the typed-ABox SHOIQ certificate.
# Submit as --array=0-3 after staging the immutable binary and harness.
#SBATCH --job-name=km-6934-ni-abox
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/6934-ni-abox-v1/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/6934-ni-abox-v1
km_root=/ibex/scratch/hohndor/km
expected_binary=cfb0c376dc6ce745e3343d66faec17b05600e7a7aaa675f948a9761f20dfb9e0
ontologies=(
  ore_ont_6934.owl
  ore_ont_10702.owl
  ore_ont_15846.owl
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

work=${SLURM_TMPDIR:-/tmp}/km-6934-ni-abox-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}
/usr/bin/mkdir -p "$work/run" "$root/results" "$root/failures"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_6934_ni_abox_gate \
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
if row.get("ont") != sys.argv[2]:
    raise SystemExit(f"ontology provenance mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"exact gate failed: {row}")
PY
/usr/bin/mv "$root/results/$ontology.ibex.json.tmp" "$root/results/$ontology.ibex.json"
echo "TASK_COMPLETE ontology=$ontology"
