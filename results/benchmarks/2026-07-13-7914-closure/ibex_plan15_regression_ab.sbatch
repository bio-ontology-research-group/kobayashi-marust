#!/bin/bash
#SBATCH --job-name=p15-reg-ab
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/plan15_7914_closure/ab-%A_%a.out

set -u

km_root=/ibex/scratch/hohndor/km
root=$km_root/plan15_7914_closure
corpus=$km_root/corpus
gold=$km_root/gold
compare=$km_root/fullsweep/cmp_gold.py
ontologies=(
  ore_ont_1016.owl
  ore_ont_10908.owl
  ore_ont_11623.owl
  ore_ont_11978.owl
  ore_ont_12141.owl
  ore_ont_15672.owl
  ore_ont_4054.owl
  ore_ont_5303.owl
  ore_ont_6934.owl
  ore_ont_7127.owl
  ore_ont_7581.owl
  ore_ont_8730.owl
  ore_ont_8864.owl
  ore_ont_9024.owl
  ore_ont_9635.owl
  ore_ont_541.owl
  ore_ont_12653.owl
  ore_ont_9663.owl
)

count=${#ontologies[@]}
index=${SLURM_ARRAY_TASK_ID:-0}
variant_index=$((index / count))
ontology=${ontologies[$((index % count))]}
if [ "$variant_index" -eq 0 ]; then
  variant=previous
  binary=${KM_AB_PREVIOUS_BINARY:-$km_root/engine/target/release/km}
else
  variant=plan15
  binary=${KM_AB_CANDIDATE_BINARY:-$root/km-plan15-bullseye}
fi
if [ -n "${KM_AB_SUFFIX:-}" ]; then
  variant=$variant-$KM_AB_SUFFIX
fi

result_dir=$root/ab_res
output_dir=$root/ab_out
mkdir -p "$result_dir" "$output_dir"
output=$output_dir/${ontology}__${variant}.json
stderr=$output_dir/${ontology}__${variant}.stderr
timefile=$output_dir/${ontology}__${variant}.time
result=$result_dir/${ontology}__${variant}.jsonl
input=$corpus/$ontology
gold_signature=$gold/konclude__$ontology.sig.gz
sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
debug=()
if [ "${KM_AB_DEBUG:-0}" = 1 ]; then
  debug+=(KM_HT_STATS=1)
  debug+=(KM_BRIDGE_PROGRESS=1)
  debug+=(KM_BRIDGE_SAT_RESIDUE=1)
  debug+=(KM_SAT_DEBUG=1)
fi

start=$SECONDS
/usr/bin/time -v -o "$timefile" \
  /usr/bin/timeout -k 5 "${KM_AB_TIMEOUT_S:-240}" \
  /usr/bin/env \
    KM_TRIGGER_ABSORB=1 \
    KM_KEEP_CHAIN_AXIOMS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=30 \
    KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_SATURATION_BUDGET_S=180 \
    KM_HT_MEM_GB=18 \
    KM_PAR_MEM_GB=18 \
    KM_THREADS=16 \
    "${debug[@]}" \
    "$binary" classify "$input" \
    > "$output" 2> "$stderr"
rc=$?
wall=$((SECONDS - start))
peak_kb=$(/usr/bin/grep -oE 'Maximum resident set size .kbytes.: [0-9]+' \
  "$timefile" 2>/dev/null | /usr/bin/grep -oE '[0-9]+$')

if [ "$rc" -eq 124 ]; then
  status=timeout
elif [ "$rc" -ne 0 ]; then
  status=error
elif /usr/bin/grep -q '"consistent"' "$output" 2>/dev/null; then
  status=ok
else
  status=nojson
fi
if [ "$status" = ok ]; then
  read -r verdict extra missing < <(/usr/bin/python3 "$compare" "$output" "$gold_signature")
else
  verdict=$status
  extra=0
  missing=0
fi

/usr/bin/printf '{"ont":"%s","variant":"%s","status":"%s","verdict":"%s","extra":%s,"miss":%s,"wall_s":%s,"peak_kb":%s,"rc":%s,"binary_sha256":"%s"}\n' \
  "$ontology" "$variant" "$status" "$verdict" "${extra:-0}" "${missing:-0}" \
  "$wall" "${peak_kb:-0}" "$rc" "$sha256" > "$result"
echo "DONE ontology=$ontology variant=$variant status=$status verdict=$verdict wall=$wall peak_kb=${peak_kb:-0}"
