#!/bin/bash
# Replay every selected documented route configuration with one reproducible,
# portable current binary. Historical executable paths are provenance only.
#SBATCH --job-name=km-repro-selected
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:35:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-591%36
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/route-confirmation-20260721/reproducible-current/slurm/%A_%a.out

set -euo pipefail

echo "DISABLED: this pre-closure driver inherits ambient KM/oracle state; use a hash-named closed driver bound to the final capsule" >&2
exit 2

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
asset_root=$routing_root/route-confirmation-20260721
registry=$asset_root/ontology-solve-routes.tsv
validator=$asset_root/validate_documented_route.py
runner=$routing_root/special-iri-fix-20260718/tools/validate_tail_runner.py
fingerprint=$routing_root/special-iri-fix-20260718/tools/fingerprint_tail_fulliri.py
konclude=$km_root/Konclude-official
hermit_java=$km_root/bench/jdk8u492-b09/bin/java
hermit_oracle=$km_root/bench/Oracle.class
hermit_classpath=$km_root/bench:$km_root/bench/hermit_cp/'*'
core_root=$routing_root/tail-validation-20260718/cores
current_binary=${KM_REPRO_BINARY:?set KM_REPRO_BINARY to the portable executable}
current_binary_sha=${KM_REPRO_BINARY_SHA256:?set KM_REPRO_BINARY_SHA256}
source_manifest_sha=${KM_REPRO_SOURCE_MANIFEST_SHA256:?set KM_REPRO_SOURCE_MANIFEST_SHA256}
build_receipt=${KM_REPRO_BUILD_RECEIPT:?set KM_REPRO_BUILD_RECEIPT}
build_receipt_sha=${KM_REPRO_BUILD_RECEIPT_SHA256:?set KM_REPRO_BUILD_RECEIPT_SHA256}
if [[ ! $current_binary_sha =~ ^[0-9a-f]{64}$ ]]; then
    echo "invalid KM_REPRO_BINARY_SHA256: $current_binary_sha" >&2
    exit 2
fi
validation_root=$asset_root/reproducible-current-${current_binary_sha}

/usr/bin/mkdir -p "$validation_root/results" "$validation_root/failures" \
    "$validation_root/slurm"

/usr/bin/python3 "$validator" \
    --registry "$registry" \
    --row-index "${SLURM_ARRAY_TASK_ID:-0}" \
    --km-root "$km_root" \
    --runner "$runner" \
    --fingerprint "$fingerprint" \
    --konclude "$konclude" \
    --hermit-java "$hermit_java" \
    --hermit-oracle "$hermit_oracle" \
    --hermit-classpath "$hermit_classpath" \
    --core-root "$core_root" \
    --result-dir "$validation_root" \
    --binary-override "$current_binary" \
    --binary-override-sha256 "$current_binary_sha" \
    --source-manifest-sha256 "$source_manifest_sha" \
    --build-receipt "$build_receipt" \
    --build-receipt-sha256 "$build_receipt_sha" \
    --timeout 240 \
    --memcap-mb 20480 \
    --reference-memcap-mb "${KM_REFERENCE_MEMCAP_MB:-20480}"
