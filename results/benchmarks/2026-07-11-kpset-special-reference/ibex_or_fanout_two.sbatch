#!/bin/bash
#SBATCH --job-name=km-or-two
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --array=0-1%2
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/or-two-%A_%a.out

set -u
ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711"
KM="$ROOT/kpset_disj_ext_auto_20260710/km-or-fanout"
ONTS=(9724 14817)
ont=${ONTS[$SLURM_ARRAY_TASK_ID]}
name="ore_ont_${ont}.owl"
prefix="$OUT/$ont-or-fanout"

rm -f "$prefix.json" "$prefix.stderr" "$prefix.time" "$prefix.summary.json"
/usr/bin/time -v -o "$prefix.time" \
  timeout 420 env \
    KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=10 KM_BRIDGE_RETRY_ROUNDS=1 \
    KM_HT_SATURATION_BUDGET_S=300 KM_HT_MEM_GB=58 KM_PAR_MEM_GB=58 \
    "$KM" classify "$ROOT/corpus/$name" >"$prefix.json" 2>"$prefix.stderr"
rc=$?

status=error
verdict=not-run
extra=0
missing=0
if [ "$rc" -eq 124 ]; then
  status=timeout
elif [ "$rc" -eq 0 ] && grep -q '"consistent"' "$prefix.json"; then
  status=ok
  read -r verdict extra missing < <(python3 "$ROOT/fullsweep/cmp_gold.py" "$prefix.json" "$ROOT/gold/konclude__${name}.sig.gz")
fi
printf '{"ontology":%s,"variant":"or-fanout","status":"%s","verdict":"%s","extra":%s,"missing":%s,"rc":%s}\n' \
  "$ont" "$status" "$verdict" "$extra" "$missing" "$rc" >"$prefix.summary.json"
cat "$prefix.summary.json"
