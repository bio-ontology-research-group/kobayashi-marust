#!/bin/bash
#SBATCH --job-name=km-resolved-ids3
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=96G
#SBATCH --array=0-2%3
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/resolved-ids-%A_%a.out

set -u

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711"
KM="$ROOT/kpset_disj_ext_auto_20260710/km-signed-inverse-ibex"
ONTS=(3215 7914 9663)

ont=${ONTS[$SLURM_ARRAY_TASK_ID]}
name="ore_ont_${ont}.owl"
input="$ROOT/corpus/$name"
gold="$ROOT/gold/konclude__${name}.sig.gz"
prefix="$OUT/$ont-resolved-ids"

mkdir -p "$OUT"
rm -f "$prefix.json" "$prefix.stderr" "$prefix.time" "$prefix.summary.json"
echo "BEGIN ont=$ont host=$(hostname) date=$(date -Is) sha256=$(sha256sum "$KM" | cut -d' ' -f1)"
/usr/bin/time -v -o "$prefix.time" \
  timeout 660 env \
    KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=10 KM_BRIDGE_RETRY_ROUNDS=1 \
    KM_HT_SATURATION_BUDGET_S=600 KM_HT_MEM_GB=88 KM_PAR_MEM_GB=88 \
    "$KM" classify "$input" >"$prefix.json" 2>"$prefix.stderr"
rc=$?

status=error
verdict=not-run
extra=0
missing=0
if [ "$rc" -eq 124 ]; then
  status=timeout
elif [ "$rc" -eq 0 ] && grep -q '"consistent"' "$prefix.json"; then
  status=ok
  read -r verdict extra missing < <(python3 "$ROOT/fullsweep/cmp_gold.py" "$prefix.json" "$gold")
fi
peak_kb=$(grep -oE 'Maximum resident set size .kbytes.: [0-9]+' "$prefix.time" 2>/dev/null | grep -oE '[0-9]+$')
elapsed=$(grep -oE 'Elapsed .wall clock. time .*: .*' "$prefix.time" 2>/dev/null | sed 's/^.*): //')
printf '{"ontology":%s,"variant":"resolved-ids","status":"%s","verdict":"%s","extra":%s,"missing":%s,"rc":%s,"elapsed":"%s","peak_kb":%s}\n' \
  "$ont" "$status" "$verdict" "$extra" "$missing" "$rc" "$elapsed" "${peak_kb:-0}" \
  >"$prefix.summary.json"
cat "$prefix.summary.json"
echo "END ont=$ont date=$(date -Is)"
