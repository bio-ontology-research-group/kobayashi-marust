#!/bin/bash
# Independent post-sweep audit for captured production/profile route agreement.
# Submit with --dependency=afterany:<array>_* and ARRAY_JOB_ID=<array>.
#SBATCH --job-name=km-v12-route-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=ALL
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v12-full-20260731/slurm-%x-%j.out

set -euo pipefail
: "${ARRAY_JOB_ID:?submit with the ontology array job id}"
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v12-full-20260731
km_root=/ibex/scratch/hohndor/km
audit=$root/audit_full_sweep_route_consistency.py
expected_audit=7e70f70bd8f4968ef541dd57a596904d0dec6fb64ae3cc34bf9f1c02dc61c044

test "$(/usr/bin/sha256sum "$audit" | /usr/bin/cut -d' ' -f1)" = "$expected_audit"
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

/usr/bin/python3 "$audit" \
  --root "$root" \
  --ontology-list "$km_root/routing_20260715/onts.txt" \
  --array-job-id "$ARRAY_JOB_ID" \
  --binary "$root/km" \
  --require-route-trace \
  --allow-missing-route-trace ore_ont_10860.owl \
  "${expected_nonmatches[@]}"
