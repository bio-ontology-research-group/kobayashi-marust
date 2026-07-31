#!/bin/bash
#SBATCH --job-name=km-4703045-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/rule-clash-4703045/audit-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715/rule-clash-4703045
km_root=/ibex/scratch/hohndor/km
array_job_id=${ARRAY_JOB_ID:?submit with --export=ALL,ARRAY_JOB_ID=...}

/usr/bin/python3 "$root/audit_full_sweep.py" \
  --root "$root" \
  --ontology-list "$km_root/routing_20260715/onts.txt" \
  --array-job-id "$array_job_id" \
  --binary "$root/km" \
  --require-route-trace \
  --expected-nonmatch ore_ont_2669.owl:ok:consistency_mismatch \
  --expected-nonmatch ore_ont_15516.owl:ok:consistency_mismatch \
  --expected-nonmatch ore_ont_10860.owl:ok:nogold \
  --expected-nonmatch ore_ont_1194.owl:error:error \
  --expected-nonmatch ore_ont_4669.owl:timeout:timeout
