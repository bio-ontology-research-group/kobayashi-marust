#!/bin/bash
# Ontology-major paired procedure matrix. Each ontology's arms run on one
# exclusive Cascade Lake node, so KM/Konclude time and memory comparisons do
# not mix CPU generations or compete with unrelated jobs.
#SBATCH --job-name=km-route-matrix2
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=12:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-591%36
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/matrix-gated-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
list=$root/onts.txt
runner=$root/bench_one.py
km=$root/km-profiled-gated
kon=$km_root/Konclude-official
gold_dir=$km_root/gold
result_dir=$root/matrix-results-gated
profile_dir=$root/profiles
failure_dir=$root/failures-gated
mkdir -p "$result_dir" "$profile_dir" "$failure_dir" "$root/slurm"

mapfile -t ontologies < "$list"
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
source_ontology=$km_root/corpus/$ontology
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$source_ontology" "$local_ontology"

result=$result_dir/$ontology.jsonl
profile=$profile_dir/$ontology.json
work=${SLURM_TMPDIR:-/tmp}/km-routing-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}
mkdir -p "$work"
: > "$result"

km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
kon_sha=$(/usr/bin/sha256sum "$kon" | /usr/bin/cut -d' ' -f1)
gold=$gold_dir/konclude__$ontology.sig.gz

# The exact profile consumed by the future production router. Profiling is not
# part of any arm's wall/RSS measurement.
if [[ ! -s "$profile" ]]; then
  /usr/bin/timeout -k 5 900 /usr/bin/env KM_KEEP_CHAIN_AXIOMS=1 \
    "$km" profile "$local_ontology" > "$profile"
fi

run_km() {
  local arm=$1
  shift
  local argv=(
    /usr/bin/python3 "$runner"
    --kind km --arm "$arm" --ontology "$local_ontology"
    --binary "$km" --binary-sha "$km_sha"
    --gold "$gold" --workdir "$work" --failures-dir "$failure_dir"
    --order-index "${km_position:--1}"
    --timeout 240 --memcap-mb 20480
    # The matrix measures the explicit arm below. It must never invoke the
    # learned/default route, which would normalize these settings a second time.
    --env KM_ROUTE=manual --env KM_THREADS=16 --env KM_PAR_MEM_GB=18
    --env KM_HT_MEM_GB=18
    --env KM_KEEP_CHAIN_AXIOMS=1
  )
  for setting in "$@"; do
    argv+=(--env "$setting")
  done
  "${argv[@]}" >> "$result"
}

run_konclude() {
  local workers=$1
  /usr/bin/python3 "$runner" \
    --kind konclude --arm "konclude_w${workers}" --ontology "$local_ontology" \
    --binary "$kon" --binary-sha "$kon_sha" --workers "$workers" \
    --workdir "$work" --failures-dir "$failure_dir" \
    --timeout 240 --memcap-mb 20480 >> "$result"
}

# Put one reference on each side of the KM panel. Alternate which thread count
# goes first so neither Konclude configuration gets a systematic cold-cache
# position. The ontology itself is already on node-local storage.
if (( SLURM_ARRAY_TASK_ID % 2 == 0 )); then
  run_konclude 1
else
  run_konclude 16
fi

run_named_arm() {
  case "$1" in
    default)
      run_km default
      ;;
    default8)
      run_km default8 KM_THREADS=8
      ;;
    default1)
      run_km default1 KM_THREADS=1
      ;;
    production_all)
      run_km production_all KM_TRIGGER_ABSORB=1 KM_BRIDGE_PROBE_BUDGET_S=30 \
        KM_BRIDGE_RETRY_ROUNDS=0 KM_HT_SATURATION_BUDGET_S=180
      ;;
    production_all8)
      run_km production_all8 KM_THREADS=8 KM_TRIGGER_ABSORB=1 \
        KM_BRIDGE_PROBE_BUDGET_S=30 KM_BRIDGE_RETRY_ROUNDS=0 \
        KM_HT_SATURATION_BUDGET_S=180
      ;;
    production_all1)
      run_km production_all1 KM_THREADS=1 KM_TRIGGER_ABSORB=1 \
        KM_BRIDGE_PROBE_BUDGET_S=30 KM_BRIDGE_RETRY_ROUNDS=0 \
        KM_HT_SATURATION_BUDGET_S=180
      ;;
    cb_plain16)
      run_km cb_plain16 KM_NO_ELC=1 KM_NO_HT_RACE=1 \
        KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0
      ;;
    cb_plain8)
      run_km cb_plain8 KM_NO_ELC=1 KM_NO_HT_RACE=1 \
        KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 KM_THREADS=8
      ;;
    cb_plain1)
      run_km cb_plain1 KM_NO_ELC=1 KM_NO_HT_RACE=1 \
        KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 KM_THREADS=1
      ;;
    cb_absorb16)
      run_km cb_absorb16 KM_NO_ELC=1 KM_NO_HT_RACE=1 \
        KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=1
      ;;
    cb_absorb_portfolio16)
      run_km cb_absorb_portfolio16 KM_NO_ELC=1 KM_NO_HT_RACE=1 KM_ABSORB=1
      ;;
    elc_cert)
      run_km elc_cert KM_NO_HT_RACE=1 KM_NO_ABSORB_PORTFOLIO=1 \
        KM_ABSORB=0 KM_ELC_FORCE=1 KM_ELC_CERT=2
      ;;
    lean)
      run_km lean KM_NO_ELC_PORTFOLIO=1 KM_NO_HT_RACE=1 \
        KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 KM_NO_CENTRAL=1 KM_THREADS=1
      ;;
    ht_general)
      run_km ht_general KM_NO_ELC=1 KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 \
        KM_NO_HT_QO_ROUTER=1 KM_NO_HT_SHOQ=1 KM_NO_HT_CARD=1 KM_HT_MODE=race
      ;;
    ht_qo)
      run_km ht_qo KM_NO_ELC=1 KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 \
        KM_NO_HT_SHOQ=1 KM_NO_HT_CARD=1 KM_HT_MODE=race
      ;;
    ht_shoq)
      run_km ht_shoq KM_NO_ELC=1 KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 \
        KM_NO_HT_QO_ROUTER=1 KM_NO_HT_CARD=1 KM_HT_MODE=race
      ;;
    ht_card)
      run_km ht_card KM_NO_ELC=1 KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 \
        KM_NO_HT_QO_ROUTER=1 KM_NO_HT_SHOQ=1 KM_HT_MODE=race
      ;;
    ht_bridge)
      run_km ht_bridge KM_NO_ELC=1 KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 \
        KM_NO_HT_QO_ROUTER=1 KM_NO_HT_SHOQ=1 KM_NO_HT_CARD=1 \
        KM_TRIGGER_ABSORB=1 KM_BRIDGE_PROBE_BUDGET_S=30 \
        KM_BRIDGE_RETRY_ROUNDS=0 KM_HT_SATURATION_BUDGET_S=180 KM_HT_MODE=race
      ;;
    ht_rules)
      run_km ht_rules KM_NO_ELC=1 KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 \
        KM_NO_HT_RACE=1 KM_NO_HT_QO_ROUTER=1 KM_NO_HT_SHOQ=1 KM_NO_HT_CARD=1
      ;;
    *)
      /usr/bin/printf 'unknown KM arm: %s\n' "$1" >&2
      return 2
      ;;
  esac
}

# Rotate the KM panel by ontology. Across 592 inputs every arm occupies every
# warm/cold position 31 or 32 times, eliminating a fixed page-cache advantage.
km_arms=(default default8 default1 production_all production_all8 production_all1 \
  cb_plain16 cb_plain8 cb_plain1 cb_absorb16 cb_absorb_portfolio16 elc_cert lean \
  ht_general ht_qo ht_shoq ht_card ht_bridge ht_rules)
for ((km_position=0; km_position<${#km_arms[@]}; km_position++)); do
  arm_index=$(((SLURM_ARRAY_TASK_ID + km_position) % ${#km_arms[@]}))
  run_named_arm "${km_arms[$arm_index]}"
done

if (( SLURM_ARRAY_TASK_ID % 2 == 0 )); then
  run_konclude 16
else
  run_konclude 1
fi

/usr/bin/rm -rf "$work" "$local_ontology"
/usr/bin/printf 'DONE ontology=%s rows=%s host=%s\n' \
  "$ontology" "$(/usr/bin/wc -l < "$result")" "$(hostname)"
