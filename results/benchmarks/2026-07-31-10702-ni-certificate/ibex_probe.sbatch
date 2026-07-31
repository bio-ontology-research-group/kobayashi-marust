#!/bin/bash
# Focused exact-signature validation of the NI-premise certificate on ORE 10702.
# The binary and harness are staged under an immutable scratch root before submit.
#SBATCH --job-name=km-10702-ni
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/10702-ni-cert-v1/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/10702-ni-cert-v1
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_10702.owl
expected_binary=f2a7d50a60726c5c14f0fc1f3b4225db858749096658cd2b11539f1fc84642d9
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
if [[ $cpu_model != *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]; then
  echo "UNEXPECTED_CPU_MODEL model=[$cpu_model]" >&2
  exit 2
fi
test "$(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1)" = "$expected_binary"
test -s "$root/full_panel_run_one.py"
test -s "$root/ore_canon.py"
test -s "$root/tree_watchdog.py"
test -s "$km_root/corpus/$ontology"
test -s "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz"

work=${SLURM_TMPDIR:-/tmp}/km-10702-ni-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work/run" "$root/results" "$root/failures"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_10702_ni_certificate \
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
  --env KM_ROUTE=manual \
  --env KM_MECHANISM=ht \
  --env KM_HT_ONLY=no_blocking_shoiq \
  --env KM_HT_CERT_NO_BLOCKING=1 \
  --env KM_HT_CERT_TBOX_ONLY=1 \
  --env KM_KEEP_CHAIN_AXIOMS=1 \
  --env KM_NO_HT_CARD=1 \
  --env KM_HT_BLOCK=1 \
  --env KM_NO_BOTTOM_PREPASS=1 \
  > "$root/results/$ontology.ibex.json.tmp"

/usr/bin/python3 - "$root/results/$ontology.ibex.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2]:
    raise SystemExit(f"ontology provenance mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
PY
/usr/bin/mv "$root/results/$ontology.ibex.json.tmp" "$root/results/$ontology.ibex.json"
echo "TASK_COMPLETE ontology=$ontology"
