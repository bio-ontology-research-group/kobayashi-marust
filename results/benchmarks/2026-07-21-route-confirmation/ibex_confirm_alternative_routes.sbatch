#!/bin/bash
# Revalidate every route listed in `other_verified_exact_routes` with one
# current hash-pinned KM candidate and the fresh full-IRI Konclude references.
# The 10,755-row manifest is submitted in two arrays by setting TASK_OFFSET.
#SBATCH --job-name=km-alt-confirm
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:25:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-9999%48
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/route-confirmation-20260721/alternative-slurm/%A_%a.out

set -euo pipefail

echo "DISABLED: alternatives require a hash-pinned selected-result manifest and the final closed capsule driver" >&2
exit 2

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
asset_root=$routing_root/route-confirmation-20260721
current_binary_sha=${KM_REPRO_BINARY_SHA256:?set KM_REPRO_BINARY_SHA256}
if [[ ! $current_binary_sha =~ ^[0-9a-f]{64}$ ]]; then
    echo "invalid KM_REPRO_BINARY_SHA256: $current_binary_sha" >&2
    exit 2
fi
validation_root=$asset_root/reproducible-current-${current_binary_sha}
manifest=$validation_root/alternative-route-manifest.tsv
validator=$asset_root/validate_alternative_route.py
runner=$routing_root/special-iri-fix-20260718/tools/validate_tail_runner.py
fingerprint=$routing_root/special-iri-fix-20260718/tools/fingerprint_tail_fulliri.py
offset=${TASK_OFFSET:-0}
row_index=$((offset + ${SLURM_ARRAY_TASK_ID:-0}))

/usr/bin/mkdir -p "$validation_root/alternative-results" \
    "$validation_root/alternative-failures" \
    "$validation_root/alternative-slurm"

/usr/bin/python3 "$validator" \
    --manifest "$manifest" \
    --row-index "$row_index" \
    --km-root "$km_root" \
    --runner "$runner" \
    --fingerprint "$fingerprint" \
    --selected-result-dir "$validation_root" \
    --result-dir "$validation_root" \
    --timeout 240 \
    --memcap-mb 20480
