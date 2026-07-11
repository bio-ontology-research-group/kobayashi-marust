#!/bin/bash
#SBATCH --job-name=km-7914-sat-ext-ablate
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:04:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --array=0-1%2
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/sat-ext-%A_%a.out

set -u
ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711"
KM="$ROOT/kpset_disj_ext_auto_20260710/km"
variants=(no-all no-functional)
variant=${variants[$SLURM_ARRAY_TASK_ID]}
prefix="$OUT/7914-$variant"
extra=()
if [ "$variant" = no-all ]; then
  extra+=(KM_HT_NO_SAT_ALL_EXTENSION=1)
else
  extra+=(KM_HT_NO_SAT_FUNCTIONAL_EXTENSION=1)
fi

rm -f "$prefix.json" "$prefix.stderr" "$prefix.time"
/usr/bin/time -v -o "$prefix.time" \
  timeout 160 env \
    KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 \
    KM_HT_SATURATION_BUDGET_S=120 KM_HT_MEM_GB=58 KM_PAR_MEM_GB=58 \
    "${extra[@]}" "$KM" classify "$ROOT/corpus/ore_ont_7914.owl" \
    >"$prefix.json" 2>"$prefix.stderr"
rc=$?
printf '{"ontology":7914,"variant":"%s","rc":%s}\n' "$variant" "$rc" >"$prefix.summary.json"
cat "$prefix.summary.json"
