#!/bin/bash
#SBATCH --job-name=km-3215-sweep
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/3215_closure_20260713/slurm/sweep-%A_%a.out

set -u

km_root=/ibex/scratch/hohndor/km
root=$km_root/3215_closure_20260713
binary=${KM_SWEEP_BINARY:-$root/km-3215-bullseye}
config=${KM_SWEEP_CONFIG:-3215-kpset-barrier}
corpus=$km_root/corpus
gold=$km_root/gold
compare=$km_root/fullsweep/cmp_gold.py
ontology_list=${KM_SWEEP_ONTOLOGIES:-$root/onts.txt}
result_dir=${KM_SWEEP_RESULT_DIR:-$root/res}
output_dir=${KM_SWEEP_OUTPUT_DIR:-$root/out}
mkdir -p "$result_dir" "$output_dir" "$root/slurm"

mapfile -t ontologies < "$ontology_list"
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
[ -n "${ontology:-}" ] || exit 0
input=$corpus/$ontology
[ -f "$input" ] || { echo "missing $input"; exit 2; }

output=$output_dir/$ontology.json
stderr=$output_dir/$ontology.stderr
timefile=$output_dir/$ontology.time
result=$result_dir/$ontology.jsonl
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

solved=0
if [ "$status" = ok ] && { [ "$verdict" = match ] || [ "$verdict" = nogold ] || [ "$verdict" = incons ]; }; then
  solved=1
fi

/usr/bin/printf '{"ont":"%s","config":"%s","status":"%s","verdict":"%s","extra":%s,"miss":%s,"solved":%s,"wall_s":%s,"peak_kb":%s,"rc":%s,"binary_sha256":"%s"}\n' \
  "$ontology" "$config" "$status" "$verdict" "${extra:-0}" "${missing:-0}" "$solved" \
  "$wall" "${peak_kb:-0}" "$rc" "$sha256" > "$result"

if [ "$status" = ok ]; then
  rm -f "$output" "$timefile" "$stderr"
fi
echo "DONE ontology=$ontology status=$status verdict=$verdict wall=$wall peak_kb=${peak_kb:-0}"
