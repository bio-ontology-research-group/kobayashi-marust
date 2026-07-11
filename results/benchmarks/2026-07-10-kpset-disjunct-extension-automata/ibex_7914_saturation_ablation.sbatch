#!/bin/bash
#SBATCH --job-name=km-7914-sat-ablate
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --array=0-1%2
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_disj_ext_auto_20260710/slurm-%A_%a.out

set -u

ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_disj_ext_auto_20260710"
KM="$OUT/km"
input="$ROOT/corpus/ore_ont_7914.owl"
gold="$ROOT/gold/konclude__ore_ont_7914.owl.sig.gz"
variants=(no-satcache no-saturation)
variant=${variants[$SLURM_ARRAY_TASK_ID]}
prefix="$OUT/7914-$variant"

extra_env=(KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1)
if [ "$variant" = no-satcache ]; then
  extra_env+=(KM_HT_NO_SATCACHE=1)
else
  extra_env+=(KM_HT_NO_SATURATION=1)
fi

rm -f "$prefix.json" "$prefix.stderr" "$prefix.time" "$prefix.summary.json"
echo "BEGIN variant=$variant host=$(hostname) date=$(date -Is) sha256=$(sha256sum "$KM" | cut -d' ' -f1)"
/usr/bin/time -v -o "$prefix.time" \
  timeout 1080 env "${extra_env[@]}" \
    KM_BRIDGE_PROBE_BUDGET_S=10 KM_BRIDGE_RETRY_ROUNDS=1 KM_PAR_MEM_GB=58 \
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
printf '{"ontology":7914,"variant":"%s","status":"%s","verdict":"%s","extra":%s,"missing":%s,"rc":%s,"elapsed":"%s","peak_kb":%s}\n' \
  "$variant" "$status" "$verdict" "$extra" "$missing" "$rc" "$elapsed" "${peak_kb:-0}" \
  >"$prefix.summary.json"
cat "$prefix.summary.json"
