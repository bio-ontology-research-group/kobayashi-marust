#!/bin/bash
#SBATCH --job-name=km-7914-extract-ab
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --array=0-1%2
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/extractor-%A_%a.out

set -u
ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711"
KM="$ROOT/kpset_disj_ext_auto_20260710/km-extractor-parity"
variants=(guarded trust)
variant=${variants[$SLURM_ARRAY_TASK_ID]}
prefix="$OUT/7914-extractor-$variant"
input="$ROOT/corpus/ore_ont_7914.owl"
gold="$ROOT/gold/konclude__ore_ont_7914.owl.sig.gz"
trust=()
if [ "$variant" = trust ]; then
  trust=(KM_HT_TRUST_SAT_AUTOMATA=1)
fi

rm -f "$prefix.json" "$prefix.stderr" "$prefix.time" "$prefix.summary.json"
/usr/bin/time -v -o "$prefix.time" \
  timeout 90 env \
    KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=10 KM_BRIDGE_RETRY_ROUNDS=1 \
    KM_HT_SATURATION_BUDGET_S=120 KM_HT_MEM_GB=58 KM_PAR_MEM_GB=58 \
    "${trust[@]}" "$KM" classify "$input" >"$prefix.json" 2>"$prefix.stderr"
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
printf '{"ontology":7914,"variant":"extractor-%s","status":"%s","verdict":"%s","extra":%s,"missing":%s,"rc":%s}\n' \
  "$variant" "$status" "$verdict" "$extra" "$missing" "$rc" >"$prefix.summary.json"
cat "$prefix.summary.json"
