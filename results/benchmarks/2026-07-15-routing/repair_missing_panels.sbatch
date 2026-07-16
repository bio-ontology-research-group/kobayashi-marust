#!/bin/bash
# Repair the 13 panels lost when shard tasks 5 and 6 exceeded their allocation.
# Each procedure runs in a separate Slurm step so a runaway process cannot kill
# the panel allocation or leave descendants charged to the next procedure.
# Slurm steps on IBEX have private /tmp namespaces, so the ontology and partial
# panel must live on shared scratch rather than under SLURM_TMPDIR.
# The binary, runner, contract, arm rotation, and output directories are the
# frozen c229366f matrix inputs.
#SBATCH --job-name=km-routing-repair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=03:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-12%13
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/repair-c229-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix-3b1d2a87.py
contract=$root/matrix_contract.py
validator=$root/validate_matrix_panel.py
km=$root/km-source-symbol-c229366f
kon=$km_root/Konclude-official
gold_dir=$km_root/gold
result_dir=$root/matrix-results-c229366f
profile_dir=$root/profiles-schema2-positiveabox1
failure_dir=$root/failures-c229366f
manifest_dir=$root/manifests-c229366f-repair
work_root=$root/repair-work-c229366f

bench=$km_root/bench
java=$bench/jdk8u492-b09/bin/java
elk=$bench/reasoners/elk-distribution-cli-0.6.0/elk.jar
hermit_oracle=$bench/Oracle.class
hermit_classpath=$bench:$bench/hermit_cp/'*'

missing=(
  ore_ont_2228.owl
  ore_ont_3524.owl
  ore_ont_3770.owl
  ore_ont_5089.owl
  ore_ont_5090.owl
  ore_ont_6207.owl
  ore_ont_7639.owl
  ore_ont_8369.owl
  ore_ont_8806.owl
  ore_ont_15703.owl
  ore_ont_16167.owl
  ore_ont_16626.owl
  ore_ont_16777.owl
)

/usr/bin/mkdir -p \
  "$result_dir" "$failure_dir" "$manifest_dir" "$work_root" "$root/slurm"
mapfile -t panel_arms < <(/usr/bin/python3 "$contract")
mapfile -t all_ontologies < "$root/onts.txt"
[[ ${#panel_arms[@]} -eq 28 ]] || { echo "arm contract is not 28 rows" >&2; exit 2; }

ontology=${missing[${SLURM_ARRAY_TASK_ID:-0}]}
global_index=-1
for index in "${!all_ontologies[@]}"; do
  if [[ "${all_ontologies[$index]}" == "$ontology" ]]; then
    global_index=$index
    break
  fi
done
[[ $global_index -ge 0 ]] || { echo "ontology absent from frozen list: $ontology" >&2; exit 2; }

source_ontology=$km_root/corpus/$ontology
gold=$gold_dir/konclude__$ontology.sig.gz
profile=$profile_dir/$ontology.json
result=$result_dir/$ontology.jsonl
work=$work_root/km-routing-repair-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}
local_ontology=$work/$ontology
panel=$work/$ontology.jsonl.partial
/usr/bin/rm -rf "$work"
/usr/bin/mkdir -p "$work"
/usr/bin/cp "$source_ontology" "$local_ontology"
: > "$panel"
trap '/usr/bin/rm -rf "$work"' EXIT

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

case "$ontology" in
  ore_ont_15703.owl|ore_ont_3524.owl)
    [[ ! -s "$gold" ]] || { echo "no-gold ontology unexpectedly has gold" >&2; exit 2; }
    gold_args=(--gold-kind none)
    ;;
  *)
    [[ -s "$gold" ]] || { echo "missing frozen Konclude gold: $ontology" >&2; exit 2; }
    gold_args=(--gold "$gold" --gold-kind konclude)
    ;;
esac

manifest=$manifest_dir/task-${SLURM_ARRAY_JOB_ID:-$SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}.txt
{
  /usr/bin/printf 'job_id=%s\narray_job_id=%s\ntask_id=%s\nhost=%s\nontology=%s\nglobal_index=%s\n' \
    "$SLURM_JOB_ID" "${SLURM_ARRAY_JOB_ID:-$SLURM_JOB_ID}" \
    "$SLURM_ARRAY_TASK_ID" "$(hostname)" "$ontology" "$global_index"
  /usr/bin/printf 'km_sha=%s\nkonclude_sha=%s\nelk_sha=%s\nhermit_sha=%s\njava_sha=%s\n' \
    "$km_sha" "$kon_sha" "$elk_sha" "$hermit_sha" "$java_sha"
} > "$manifest"

run_step() {
  srun --exclusive --nodes=1 --ntasks=1 --cpus-per-task=16 \
    --mem=20G --kill-on-bad-exit=0 "$@"
}

# Fail before recording any measurements if the step namespace cannot read the
# shared ontology. Konclude exits successfully on a missing input and would
# otherwise make an invalid panel look structurally complete.
run_step /usr/bin/test -s "$local_ontology"

for ((panel_position=0; panel_position<${#panel_arms[@]}; panel_position++)); do
  arm_index=$(((global_index + panel_position) % ${#panel_arms[@]}))
  arm=${panel_arms[$arm_index]}
  common=(
    --arm "$arm" --ontology "$local_ontology"
    "${gold_args[@]}" --workdir "$work" --failures-dir "$failure_dir"
    --order-index "$panel_position" --timeout 240 --memcap-mb 20480
  )
  case "$arm" in
    elk)
      run_step /usr/bin/python3 "$runner" --kind elk "${common[@]}" \
        --binary "$elk" --binary-sha "$elk_sha" \
        --java "$java" --runtime-sha "$java_sha" --java-heap=-Xmx16g >> "$panel"
      ;;
    hermit)
      run_step /usr/bin/python3 "$runner" --kind hermit "${common[@]}" \
        --binary "$hermit_oracle" --binary-sha "$hermit_sha" \
        --java "$java" --runtime-sha "$java_sha" --java-heap=-Xmx16g \
        --classpath "$hermit_classpath" >> "$panel"
      ;;
    konclude_w1)
      run_step /usr/bin/python3 "$runner" --kind konclude "${common[@]}" \
        --binary "$kon" --binary-sha "$kon_sha" --workers 1 >> "$panel"
      ;;
    konclude_w16)
      run_step /usr/bin/python3 "$runner" --kind konclude "${common[@]}" \
        --binary "$kon" --binary-sha "$kon_sha" --workers 16 >> "$panel"
      ;;
    *)
      run_step /usr/bin/python3 "$runner" --kind km "${common[@]}" \
        --binary "$km" --binary-sha "$km_sha" --env "KM_ROUTE=$arm" >> "$panel"
      ;;
  esac
done

/usr/bin/python3 "$validator" "$panel" --ontology "$ontology"
if [[ -e "$result" ]]; then
  /usr/bin/mv "$result" "$result.replaced.${SLURM_JOB_ID}"
fi
/usr/bin/mv "$panel" "$result"
/usr/bin/rm -rf "$work"
trap - EXIT
/usr/bin/printf 'DONE ontology=%s rows=%s host=%s\n' \
  "$ontology" "${#panel_arms[@]}" "$(hostname)"
