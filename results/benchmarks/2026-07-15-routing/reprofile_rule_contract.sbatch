#!/bin/bash
# Reprofile only the three ORE inputs containing DL-safe rules with the final
# rule-representability statistic. The other 589 immutable profiles are linked
# into a new corpus unchanged; the original matrix profile corpus is untouched.
#SBATCH --job-name=km-rule-reprofile
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=4G
#SBATCH --array=0-2
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/rule-profile-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/routing_20260715
km_root=/ibex/scratch/hohndor/km
: "${PROFILE_KM_BIN:?submit with the immutable policy-guard binary path}"
: "${PROFILE_KM_SHA:?submit with its SHA-256}"
[[ $(/usr/bin/sha256sum "$PROFILE_KM_BIN" | /usr/bin/cut -d' ' -f1) == "$PROFILE_KM_SHA" ]]

ontologies=(ore_ont_10860.owl ore_ont_15516.owl ore_ont_2669.owl)
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
out_dir=$root/profiles-policyguard1
work=${SLURM_TMPDIR:-/tmp}/km-rule-profile-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID:-0}
/usr/bin/mkdir -p "$out_dir" "$work"

# Hard-link unchanged records once. Concurrent `cp -aln` invocations are
# idempotent, and each task replaces only its own rule profile atomically.
/usr/bin/cp -aln "$root/profiles/." "$out_dir/"
/usr/bin/cp "$km_root/corpus/$ontology" "$work/$ontology"
/usr/bin/timeout -k 5 1200 /usr/bin/env KM_ROUTE=manual KM_KEEP_CHAIN_AXIOMS=1 \
  "$PROFILE_KM_BIN" profile "$work/$ontology" > "$work/$ontology.json"
/usr/bin/mv "$work/$ontology.json" "$out_dir/$ontology.json"
/usr/bin/rm -rf "$work"
