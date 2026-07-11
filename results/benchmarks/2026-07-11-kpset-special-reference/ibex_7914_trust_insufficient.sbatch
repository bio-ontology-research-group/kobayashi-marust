#!/bin/bash
#SBATCH --job-name=km-7914-trust-insuf
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/trust-insufficient-%j.out

set -u
ROOT=/ibex/scratch/hohndor/km
OUT="$ROOT/kpset_special_ref_20260711"
KM="$ROOT/kpset_disj_ext_auto_20260710/km-signed-inverse-ibex"
prefix="$OUT/7914-trust-insufficient"

rm -f "$prefix.json" "$prefix.stderr" "$prefix.time" "$prefix.summary.json"
/usr/bin/time -v -o "$prefix.time" \
  timeout 120 env \
    KM_TRIGGER_ABSORB=1 KM_KEEP_CHAIN_AXIOMS=1 KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 \
    KM_HT_TRUST_INSUFFICIENT=1 KM_HT_SATURATION_BUDGET_S=120 \
    KM_HT_MEM_GB=58 KM_PAR_MEM_GB=58 \
    "$KM" classify "$ROOT/corpus/ore_ont_7914.owl" >"$prefix.json" 2>"$prefix.stderr"
rc=$?

status=error
verdict=not-run
extra=0
missing=0
if [ "$rc" -eq 124 ]; then
  status=timeout
elif [ "$rc" -eq 0 ] && grep -q '"consistent"' "$prefix.json"; then
  status=ok
  read -r verdict extra missing < <(python3 "$ROOT/fullsweep/cmp_gold.py" "$prefix.json" "$ROOT/gold/konclude__ore_ont_7914.owl.sig.gz")
fi
printf '{"ontology":7914,"variant":"trust-insufficient","status":"%s","verdict":"%s","extra":%s,"missing":%s,"rc":%s}\n' \
  "$status" "$verdict" "$extra" "$missing" "$rc" >"$prefix.summary.json"
cat "$prefix.summary.json"
