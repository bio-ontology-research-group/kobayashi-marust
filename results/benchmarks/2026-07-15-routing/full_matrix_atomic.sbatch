#!/bin/bash
# Ontology-major paired matrix of isolated KM mechanisms. Every KM row starts
# exactly one terminating classifier; historical portfolios/races are excluded.
# The two official Konclude references bracket the rotated KM panel on the same
# exclusive Cascade Lake node.
#SBATCH --job-name=km-atomic-matrix
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
# 23 KM mechanisms + 2 references at 240 s each have a strict 100-minute
# timeout ceiling. Three hours covers frontend and local-file overhead.
#SBATCH --time=03:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-591%36
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/atomic-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
list=$root/onts.txt
runner=$root/bench_one_matrix_frozen.py
km=$root/km-profiled-atomic1
kon=$km_root/Konclude-official
gold_dir=$km_root/gold
result_dir=$root/matrix-results-atomic1
profile_dir=$root/profiles
failure_dir=$root/failures-atomic1
mkdir -p "$result_dir" "$profile_dir" "$failure_dir" "$root/slurm"

mapfile -t ontologies < "$list"
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
source_ontology=$km_root/corpus/$ontology
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$source_ontology" "$local_ontology"

result=$result_dir/$ontology.jsonl
profile=$profile_dir/$ontology.json
work=${SLURM_TMPDIR:-/tmp}/km-atomic-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}
mkdir -p "$work"
: > "$result"

km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
kon_sha=$(/usr/bin/sha256sum "$kon" | /usr/bin/cut -d' ' -f1)
gold=$gold_dir/konclude__$ontology.sig.gz

if [[ ! -s "$profile" ]]; then
  /usr/bin/timeout -k 5 900 /usr/bin/env KM_ROUTE=manual KM_KEEP_CHAIN_AXIOMS=1 \
    "$km" profile "$local_ontology" > "$profile"
fi

run_km() {
  local arm=$1
  /usr/bin/python3 "$runner" \
    --kind km --arm "$arm" --ontology "$local_ontology" \
    --binary "$km" --binary-sha "$km_sha" \
    --gold "$gold" --workdir "$work" --failures-dir "$failure_dir" \
    --order-index "$km_position" --timeout 240 --memcap-mb 20480 \
    --env "KM_ROUTE=$arm" >> "$result"
}

run_konclude() {
  local workers=$1
  /usr/bin/python3 "$runner" \
    --kind konclude --arm "konclude_w${workers}" --ontology "$local_ontology" \
    --binary "$kon" --binary-sha "$kon_sha" --workers "$workers" \
    --workdir "$work" --failures-dir "$failure_dir" \
    --timeout 240 --memcap-mb 20480 >> "$result"
}

if (( SLURM_ARRAY_TASK_ID % 2 == 0 )); then
  run_konclude 1
else
  run_konclude 16
fi

# Each entry is an isolated mechanism/configuration. The old `default`,
# `production_all`, absorbed/plain portfolio, CB/HT race, EL/CB race, and
# `tab_race` names remain callable but are deliberately absent.
km_arms=(
  elc elc_cert
  cb_plain16 cb_plain8 cb_plain1
  cb_absorb16 cb_absorb8 cb_absorb1
  cb_trigger16 cb_trigger8 cb_trigger1
  lean
  ht_general ht_qo ht_shoq ht_card ht_bridge ht_rules tableau
  card_fn nominals seq_on seq_off
)

# Rotate the mechanism panel to remove fixed warm/cold position bias.
for ((km_position=0; km_position<${#km_arms[@]}; km_position++)); do
  arm_index=$(((SLURM_ARRAY_TASK_ID + km_position) % ${#km_arms[@]}))
  run_km "${km_arms[$arm_index]}"
done

if (( SLURM_ARRAY_TASK_ID % 2 == 0 )); then
  run_konclude 16
else
  run_konclude 1
fi

/usr/bin/rm -rf "$work" "$local_ontology"
/usr/bin/printf 'DONE ontology=%s rows=%s host=%s\n' \
  "$ontology" "$(/usr/bin/wc -l < "$result")" "$(hostname)"
