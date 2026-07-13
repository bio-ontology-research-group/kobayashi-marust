#!/bin/bash
#SBATCH --job-name=km-3215-ab
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/3215_closure_20260713/slurm/ab-%A_%a.out

set -u

km_root=/ibex/scratch/hohndor/km
root=$km_root/3215_closure_20260713
corpus=$km_root/corpus
gold=$km_root/gold
compare=$km_root/fullsweep/cmp_gold.py
ontologies=(
  ore_ont_11315.owl
  ore_ont_11745.owl
  ore_ont_12414.owl
  ore_ont_3215.owl
  ore_ont_4054.owl
  ore_ont_4755.owl
  ore_ont_7127.owl
  ore_ont_8068.owl
  ore_ont_8864.owl
)

count=${#ontologies[@]}
index=${SLURM_ARRAY_TASK_ID:-0}
variant_index=$((index / count))
ontology=${ontologies[$((index % count))]}
if [ "$variant_index" -eq 0 ]; then
  variant=plan15
  binary=$km_root/plan15_7914_closure/km-plan15-kpset-bullseye
else
  variant=3215-fix
  binary=$root/km-3215-bullseye
fi

result_dir=$root/ab_res
output_dir=$root/ab_out
mkdir -p "$result_dir" "$output_dir" "$root/slurm"
output=$output_dir/${ontology}__${variant}.json
stderr=$output_dir/${ontology}__${variant}.stderr
timefile=$output_dir/${ontology}__${variant}.time
result=$result_dir/${ontology}__${variant}.jsonl
input=$corpus/$ontology
gold_signature=$gold/konclude__$ontology.sig.gz
sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)

start=$SECONDS
/usr/bin/time -v -o "$timefile" \
  /usr/bin/timeout -k 5 240 \
  /usr/bin/env \
    KM_TRIGGER_ABSORB=1 \
    KM_KEEP_CHAIN_AXIOMS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=30 \
    KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_SATURATION_BUDGET_S=180 \
    KM_HT_MEM_GB=18 \
    KM_PAR_MEM_GB=18 \
    KM_THREADS=16 \
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
