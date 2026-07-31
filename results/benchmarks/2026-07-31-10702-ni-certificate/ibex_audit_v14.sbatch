#!/bin/bash
# Complete post-sweep artifact, route, and exact-signature audit.
#SBATCH --job-name=km-v14-ni-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=ALL
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v14-full-20260731/audit-%j.out

set -euo pipefail
: "${ARRAY_JOB_ID:?submit with ARRAY_JOB_ID}"

root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v14-full-20260731
km_root=/ibex/scratch/hohndor/km
cd "$root"
/usr/bin/sha256sum -c SHA256SUMS
PYTHONPATH="$root" /usr/bin/python3 -c \
  'import audit_full_sweep, full_panel_run_one, ore_canon, tree_watchdog'

expected_nonmatches=(
  --expected-nonmatch ore_ont_1194.owl:error:error
  --expected-nonmatch ore_ont_2669.owl:ok:consistency_mismatch
  --expected-nonmatch ore_ont_4669.owl:timeout:timeout
  --expected-nonmatch ore_ont_6934.owl:error:error
  --expected-nonmatch ore_ont_7499.owl:error:error
  --expected-nonmatch ore_ont_10860.owl:unsupported:unsupported
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
