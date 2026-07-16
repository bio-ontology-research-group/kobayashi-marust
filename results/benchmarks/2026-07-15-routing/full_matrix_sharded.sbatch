#!/bin/bash
# Ontology-major benchmark of isolated KM mechanisms and external baselines.
# Fifty array tasks each own 11 or 12 complete ontology panels. Within a panel,
# all 28 arms run sequentially on the same exclusive CPU model and rotate order.
# A result file becomes visible only after the complete panel validates.
#SBATCH --job-name=km-routing-matrix
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=30:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-49%50
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/atomic3-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=${MATRIX_RUNNER:-$root/bench_one_matrix_frozen.py}
contract=$root/matrix_contract.py
validator=$root/validate_matrix_panel.py
sharder=$root/make_ontology_shards.py
profile_table=$root/profile-table.csv
km=${MATRIX_KM:-$root/km-profiled-atomic2}
kon=$km_root/Konclude-official
gold_dir=$km_root/gold
result_dir=${MATRIX_RESULT_DIR:-$root/matrix-results-atomic3}
profile_dir=${MATRIX_PROFILE_DIR:-$root/profiles}
failure_dir=${MATRIX_FAILURE_DIR:-$root/failures-atomic3}
manifest_dir=${MATRIX_MANIFEST_DIR:-$root/manifests-atomic3}

bench=$km_root/bench
java=$bench/jdk8u492-b09/bin/java
elk=$bench/reasoners/elk-distribution-cli-0.6.0/elk.jar
hermit_oracle=$bench/Oracle.class
hermit_main=$bench/hermit_cp/org.semanticweb.hermit-1.4.6.519-SNAPSHOT.jar
hermit_classpath=$bench:$bench/hermit_cp/'*'

/usr/bin/mkdir -p \
  "$result_dir" "$profile_dir" "$failure_dir" "$manifest_dir" "$root/slurm"

for required in \
  "$runner" "$contract" "$validator" "$sharder" "$profile_table" \
  "$km" "$kon" "$java" "$elk" "$hermit_oracle" "$hermit_main"
do
  [[ -s "$required" ]] || { echo "missing benchmark input: $required" >&2; exit 2; }
done

km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
kon_sha=$(/usr/bin/sha256sum "$kon" | /usr/bin/cut -d' ' -f1)
elk_sha=$(/usr/bin/sha256sum "$elk" | /usr/bin/cut -d' ' -f1)
java_sha=$(/usr/bin/sha256sum "$java" | /usr/bin/cut -d' ' -f1)
hermit_sha=$(
  {
    /usr/bin/sha256sum "$hermit_oracle"
    /usr/bin/find "$bench/hermit_cp" -maxdepth 1 -type f -name '*.jar' -print0 \
      | /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
  } | /usr/bin/sha256sum | /usr/bin/cut -d' ' -f1
)

task_id=${SLURM_ARRAY_TASK_ID:-0}
work=${SLURM_TMPDIR:-/tmp}/km-routing-${SLURM_JOB_ID}_${task_id}
/usr/bin/mkdir -p "$work"

mapfile -t panel_arms < <(/usr/bin/python3 "$contract")
mapfile -t assignments < <(
  /usr/bin/python3 "$sharder" --profiles "$profile_table" --shards 50 --task "$task_id"
)
[[ ${#panel_arms[@]} -eq 28 ]] || { echo "arm contract is not 28 rows" >&2; exit 2; }
[[ ${#assignments[@]} -ge 11 && ${#assignments[@]} -le 12 ]] \
  || { echo "shard does not contain 11 or 12 ontologies" >&2; exit 2; }

manifest=$manifest_dir/task-${SLURM_ARRAY_JOB_ID:-$SLURM_JOB_ID}_${task_id}.txt
{
  /usr/bin/printf 'job_id=%s\narray_job_id=%s\ntask_id=%s\nhost=%s\n' \
    "$SLURM_JOB_ID" "${SLURM_ARRAY_JOB_ID:-$SLURM_JOB_ID}" "$task_id" "$(hostname)"
  /usr/bin/printf 'km_sha=%s\nkonclude_sha=%s\nelk_sha=%s\nhermit_sha=%s\njava_sha=%s\n' \
    "$km_sha" "$kon_sha" "$elk_sha" "$hermit_sha" "$java_sha"
  /usr/bin/printf '%s\n' "${assignments[@]}"
} > "$manifest"

run_km() {
  local arm=$1 ontology_path=$2 panel=$3 panel_position=$4 ontology_work=$5
  /usr/bin/python3 "$runner" \
    --kind km --arm "$arm" --ontology "$ontology_path" \
    --binary "$km" --binary-sha "$km_sha" \
    "${gold_args[@]}" --workdir "$ontology_work" --failures-dir "$failure_dir" \
    --order-index "$panel_position" --timeout 240 --memcap-mb 20480 \
    --env "KM_ROUTE=$arm" >> "$panel"
}

run_konclude() {
  local arm=$1 workers=$2 ontology_path=$3 panel=$4 panel_position=$5 ontology_work=$6
  /usr/bin/python3 "$runner" \
    --kind konclude --arm "$arm" --ontology "$ontology_path" \
    --binary "$kon" --binary-sha "$kon_sha" --workers "$workers" \
    "${gold_args[@]}" --workdir "$ontology_work" --failures-dir "$failure_dir" \
    --order-index "$panel_position" --timeout 240 --memcap-mb 20480 >> "$panel"
}

run_elk() {
  local ontology_path=$1 panel=$2 panel_position=$3 ontology_work=$4
  /usr/bin/python3 "$runner" \
    --kind elk --arm elk --ontology "$ontology_path" \
    --binary "$elk" --binary-sha "$elk_sha" \
    --java "$java" --runtime-sha "$java_sha" --java-heap=-Xmx16g \
    "${gold_args[@]}" --workdir "$ontology_work" --failures-dir "$failure_dir" \
    --order-index "$panel_position" --timeout 240 --memcap-mb 20480 >> "$panel"
}

run_hermit() {
  local ontology_path=$1 panel=$2 panel_position=$3 ontology_work=$4
  /usr/bin/python3 "$runner" \
    --kind hermit --arm hermit --ontology "$ontology_path" \
    --binary "$hermit_oracle" --binary-sha "$hermit_sha" \
    --java "$java" --runtime-sha "$java_sha" --java-heap=-Xmx16g \
    --classpath "$hermit_classpath" \
    "${gold_args[@]}" --workdir "$ontology_work" --failures-dir "$failure_dir" \
    --order-index "$panel_position" --timeout 240 --memcap-mb 20480 >> "$panel"
}

for assignment in "${assignments[@]}"; do
  IFS=$'\t' read -r shard_index global_index scheduling_weight ontology <<< "$assignment"
  [[ "$shard_index" == "$task_id" ]] || { echo "bad shard assignment" >&2; exit 2; }
  source_ontology=$km_root/corpus/$ontology
  local_ontology=$work/$ontology
  result=$result_dir/$ontology.jsonl
  gold=$gold_dir/konclude__$ontology.sig.gz
  profile=$profile_dir/$ontology.json
  ontology_work=$work/panel-$global_index
  panel=$ontology_work/$ontology.jsonl.partial

  if [[ -s "$result" ]] && /usr/bin/python3 "$validator" "$result" --ontology "$ontology"; then
    /usr/bin/printf 'SKIP complete ontology=%s shard=%s\n' "$ontology" "$task_id"
    continue
  fi
  if [[ -e "$result" ]]; then
    /usr/bin/mv "$result" "$result.invalid.${SLURM_JOB_ID}"
  fi

  [[ -s "$source_ontology" ]] || { echo "missing ontology: $source_ontology" >&2; exit 2; }
  case "$ontology" in
    ore_ont_10860.owl|ore_ont_1194.owl|ore_ont_15703.owl|ore_ont_3524.owl|ore_ont_4669.owl)
      [[ ! -s "$gold" ]] \
        || { echo "frozen no-gold ontology unexpectedly has gold: $ontology" >&2; exit 2; }
      # Every arm still runs. The analyzer adjudicates canonical signature
      # hashes against HermiT instead of assuming that a parseable answer is
      # correct.
      gold_args=(--gold-kind none)
      ;;
    *)
      [[ -s "$gold" ]] \
        || { echo "missing frozen Konclude gold: $ontology" >&2; exit 2; }
      gold_args=(--gold "$gold" --gold-kind konclude)
      ;;
  esac
  /usr/bin/mkdir -p "$ontology_work"
  /usr/bin/cp "$source_ontology" "$local_ontology"
  : > "$panel"

  if [[ ! -s "$profile" ]]; then
    profile_tmp=$ontology_work/$ontology.profile.json
    /usr/bin/timeout -k 5 900 /usr/bin/env KM_ROUTE=manual KM_KEEP_CHAIN_AXIOMS=1 \
      "$km" profile "$local_ontology" > "$profile_tmp"
    /usr/bin/mv "$profile_tmp" "$profile"
  fi

  for ((panel_position=0; panel_position<${#panel_arms[@]}; panel_position++)); do
    arm_index=$(((global_index + panel_position) % ${#panel_arms[@]}))
    arm=${panel_arms[$arm_index]}
    case "$arm" in
      elk)
        run_elk "$local_ontology" "$panel" "$panel_position" "$ontology_work"
        ;;
      hermit)
        run_hermit "$local_ontology" "$panel" "$panel_position" "$ontology_work"
        ;;
      konclude_w1)
        run_konclude "$arm" 1 "$local_ontology" "$panel" "$panel_position" "$ontology_work"
        ;;
      konclude_w16)
        run_konclude "$arm" 16 "$local_ontology" "$panel" "$panel_position" "$ontology_work"
        ;;
      *)
        run_km "$arm" "$local_ontology" "$panel" "$panel_position" "$ontology_work"
        ;;
    esac
  done

  /usr/bin/python3 "$validator" "$panel" --ontology "$ontology"
  /usr/bin/mv "$panel" "$result"
  /usr/bin/rm -rf "$ontology_work" "$local_ontology"
  /usr/bin/printf 'DONE ontology=%s shard=%s weight=%s rows=%s host=%s\n' \
    "$ontology" "$task_id" "$scheduling_weight" "${#panel_arms[@]}" "$(hostname)"
done
