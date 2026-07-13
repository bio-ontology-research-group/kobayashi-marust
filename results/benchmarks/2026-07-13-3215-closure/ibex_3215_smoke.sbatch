#!/bin/bash
#SBATCH --job-name=km-3215-smoke
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/3215_closure_20260713/slurm/smoke-%j.out

set -u

km_root=/ibex/scratch/hohndor/km
root=$km_root/3215_closure_20260713
binary=$root/km-3215-bullseye
ontology=ore_ont_3215.owl
input=$km_root/corpus/$ontology
gold_signature=$km_root/gold/konclude__$ontology.sig.gz
compare=$km_root/fullsweep/cmp_gold.py
variant=${KM_SMOKE_VARIANT:-quiet16}
threads=${KM_SMOKE_THREADS:-16}
ht_nice=${KM_SMOKE_HT_NICE:-1}
output=$root/smoke/$ontology.$variant.json
stderr=$root/smoke/$ontology.$variant.stderr
timefile=$root/smoke/$ontology.$variant.time
result=$root/smoke/$ontology.$variant.result.jsonl

mkdir -p "$root/smoke" "$root/slurm"
[ -x "$binary" ] || { echo "missing executable $binary"; exit 2; }
[ -f "$input" ] || { echo "missing ontology $input"; exit 2; }
[ -f "$gold_signature" ] || { echo "missing gold $gold_signature"; exit 2; }

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
    KM_THREADS="$threads" \
    KM_HT_NICE="$ht_nice" \
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

/usr/bin/printf '{"ont":"%s","config":"3215-kpset-barrier-smoke","variant":"%s","threads":%s,"ht_nice":"%s","status":"%s","verdict":"%s","extra":%s,"miss":%s,"wall_s":%s,"peak_kb":%s,"rc":%s,"binary_sha256":"%s"}\n' \
  "$ontology" "$variant" "$threads" "$ht_nice" "$status" "$verdict" \
  "${extra:-0}" "${missing:-0}" "$wall" "${peak_kb:-0}" "$rc" "$sha256" > "$result"

echo "DONE ontology=$ontology status=$status verdict=$verdict extra=${extra:-0} missing=${missing:-0} wall=$wall peak_kb=${peak_kb:-0}"
