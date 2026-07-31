#!/bin/bash
# Submit with --dependency=afterany:<array-job-id> and
# --export=ALL,ARRAY_JOB_ID=<array-job-id>.
#SBATCH --job-name=km-adaptive-comp-v11-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=ALL
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v11-full-20260731/slurm-%x-%j.out

set -euo pipefail
: "${ARRAY_JOB_ID:?submit with the ontology array job id}"
root=${SWEEP_ROOT:-/ibex/scratch/hohndor/km/adaptive-composite-layout-v11-full-20260731}
km_root=/ibex/scratch/hohndor/km

PYTHONPATH="$root" /usr/bin/python3 -c \
  'import audit_full_sweep, full_panel_run_one, ore_canon, tree_watchdog'
/usr/bin/sha256sum -c "$root/SHA256SUMS"

expected_nonmatches=(
  --expected-nonmatch ore_ont_1194.owl:error:error
  --expected-nonmatch ore_ont_2669.owl:ok:consistency_mismatch
  --expected-nonmatch ore_ont_4669.owl:timeout:timeout
  --expected-nonmatch ore_ont_6934.owl:error:error
  --expected-nonmatch ore_ont_7499.owl:error:error
  --expected-nonmatch ore_ont_10702.owl:error:error
  --expected-nonmatch ore_ont_10860.owl:unsupported:unsupported
  --expected-nonmatch ore_ont_12653.owl:timeout:timeout
  --expected-nonmatch ore_ont_15516.owl:ok:consistency_mismatch
)

/usr/bin/python3 "$root/audit_full_sweep.py" \
  --root "$root" \
  --ontology-list "$km_root/routing_20260715/onts.txt" \
  --array-job-id "$ARRAY_JOB_ID" \
  --binary "$root/km" \
  --require-route-trace \
  --allow-missing-route-trace ore_ont_10860.owl \
  "${expected_nonmatches[@]}"
