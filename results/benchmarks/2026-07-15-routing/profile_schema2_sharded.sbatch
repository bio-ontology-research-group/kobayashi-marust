#!/bin/bash
# Recompute the immutable source-profile corpus with schema 2. Fifty tasks use
# the same ontology-major partition as the mechanism matrix; every JSON file is
# validated before an atomic rename, so interrupted tasks are safely resumable.
#SBATCH --job-name=km-profile-schema2
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=04:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=12G
#SBATCH --array=0-49%50
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/profile-schema2-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/routing_20260715
km_root=/ibex/scratch/hohndor/km
sharder=$root/make_ontology_shards.py
profile_table=$root/profile-table.csv
: "${PROFILE_KM_BIN:?submit with the immutable schema-2 km binary}"
: "${EXPECTED_KM_SHA:?submit with the binary SHA-256}"
: "${PROFILE_OUT_DIR:?submit with a new immutable profile directory}"

[[ -x "$PROFILE_KM_BIN" ]] || { echo "missing KM binary: $PROFILE_KM_BIN" >&2; exit 2; }
[[ -s "$sharder" && -s "$profile_table" ]] \
  || { echo "missing sharding input" >&2; exit 2; }
observed_sha=$(/usr/bin/sha256sum "$PROFILE_KM_BIN" | /usr/bin/cut -d' ' -f1)
[[ "$observed_sha" == "$EXPECTED_KM_SHA" ]] \
  || { echo "KM hash mismatch: $observed_sha" >&2; exit 2; }

task_id=${SLURM_ARRAY_TASK_ID:-0}
work=${SLURM_TMPDIR:-/tmp}/km-profile-schema2-${SLURM_JOB_ID}_${task_id}
time_dir=$PROFILE_OUT_DIR-times
manifest_dir=$PROFILE_OUT_DIR-manifests
/usr/bin/mkdir -p "$work" "$PROFILE_OUT_DIR" "$time_dir" "$manifest_dir"

mapfile -t assignments < <(
  /usr/bin/python3 "$sharder" --profiles "$profile_table" --shards 50 --task "$task_id"
)
[[ ${#assignments[@]} -ge 11 && ${#assignments[@]} -le 12 ]] \
  || { echo "shard does not contain 11 or 12 ontologies" >&2; exit 2; }

validate_profile() {
  /usr/bin/python3 - "$1" "$2" <<'PY'
import json
import sys

path, ontology = sys.argv[1:]
with open(path, encoding="utf-8") as handle:
    row = json.load(handle)
profile = row.get("profile")
assert row.get("ont") == ontology, (row.get("ont"), ontology)
assert row.get("status") == "ok", row
assert isinstance(profile, dict), row
assert profile.get("schema_version") == 2, profile.get("schema_version")
assert isinstance(profile.get("positive_abox_tbox_separable"), bool)
assert "bottom_occurrences" in profile.get("source", {})
assert "bottom_role_occurrences" in profile.get("source", {})
PY
}

for assignment in "${assignments[@]}"; do
  IFS=$'\t' read -r shard_index global_index scheduling_weight ontology <<< "$assignment"
  [[ "$shard_index" == "$task_id" ]] \
    || { echo "bad shard assignment for $ontology" >&2; exit 2; }
  source_ontology=$km_root/corpus/$ontology
  final=$PROFILE_OUT_DIR/$ontology.json
  final_time=$time_dir/$ontology.time
  [[ -s "$source_ontology" ]] || { echo "missing ontology: $source_ontology" >&2; exit 2; }
  if [[ -s "$final" ]] && validate_profile "$final" "$ontology"; then
    /usr/bin/printf 'SKIP ontology=%s shard=%s\n' "$ontology" "$task_id"
    continue
  fi

  local_ontology=$work/$ontology
  tmp=$work/$ontology.json
  tmp_time=$work/$ontology.time
  /usr/bin/cp "$source_ontology" "$local_ontology"
  /usr/bin/timeout -k 5 1200 \
    /usr/bin/time -v -o "$tmp_time" \
    /usr/bin/env KM_ROUTE=manual KM_KEEP_CHAIN_AXIOMS=1 \
    "$PROFILE_KM_BIN" profile "$local_ontology" > "$tmp"
  validate_profile "$tmp" "$ontology"
  /usr/bin/mv "$tmp" "$final"
  /usr/bin/mv "$tmp_time" "$final_time"
  /usr/bin/rm -f "$local_ontology"
  /usr/bin/printf 'DONE ontology=%s shard=%s index=%s\n' \
    "$ontology" "$task_id" "$global_index"
done

{
  /usr/bin/printf 'job_id=%s\narray_job_id=%s\ntask_id=%s\nhost=%s\nkm_sha=%s\n' \
    "$SLURM_JOB_ID" "${SLURM_ARRAY_JOB_ID:-$SLURM_JOB_ID}" "$task_id" \
    "$(hostname)" "$observed_sha"
  /usr/bin/printf '%s\n' "${assignments[@]}"
} > "$manifest_dir/task-${SLURM_ARRAY_JOB_ID:-$SLURM_JOB_ID}_${task_id}.txt"
