#!/bin/bash
# Exact focused acceptance gate for the feature-selected positive EL ABox route.
# Both ontologies failed under automatic nominal routing in sweep 49632438.
# The candidate binary must select the route automatically and match Konclude's
# complete canonical signature under the production limits.
#SBATCH --job-name=km-elabox-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=intel
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/positive-el-abox-20260730/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/positive-el-abox-20260730
km_root=/ibex/scratch/hohndor/km
bin=$root/km
out=$root/focused-$SLURM_JOB_ID
mkdir -p "$out"

sha256sum "$bin"
PYTHONPATH="$root" /usr/bin/python3 -c "import ore_canon" || {
  echo "EL_ABOX_GATE_SETUP_FAILED missing ore_canon"
  exit 2
}
fail=0
for id in 1579 3377; do
  ont=$km_root/corpus/ore_ont_$id.owl
  gold=$km_root/gold/konclude__ore_ont_$id.owl.sig.gz
  set +e
  env KM_ROUTE=auto KM_THREADS=16 KM_PAR_MEM_GB=18 KM_HT_MEM_GB=18 \
    /usr/bin/time -f "%e %M" -o "$out/$id.time" \
    timeout 240 "$bin" classify "$ont" \
    > "$out/$id.json" 2> "$out/$id.err"
  rc=$?
  set -e
  stats=$(/usr/bin/tail -1 "$out/$id.time" 2>/dev/null || true)
  if [[ $rc -ne 0 ]]; then
    echo "EL_ABOX_GATE ont=$id rc=$rc stats=[$stats] FAIL"
    fail=1
    continue
  fi
  verdict=$(/usr/bin/python3 "$root/kmsig.py" "$out/$id.json" "$gold" |
    /usr/bin/tr '\n' ' ') || {
      echo "EL_ABOX_GATE ont=$id rc=0 stats=[$stats] COMPARATOR_FAIL"
      fail=1
      continue
    }
  profile=$("$bin" profile "$ont" | /usr/bin/python3 -c \
    'import json,sys; d=json.load(sys.stdin); p=d["profile"]; print("route=%s el_abox=%s"%(d.get("selected_route"),p.get("positive_el_abox_materializable")))') || {
      echo "EL_ABOX_GATE ont=$id rc=0 stats=[$stats] PROFILE_FAIL"
      fail=1
      continue
    }
  echo "EL_ABOX_GATE ont=$id rc=0 stats=[$stats] $profile $verdict"
  [[ $verdict == *EXACT_MATCH* ]] || fail=1
done

if [[ $fail -ne 0 ]]; then
  echo "EL_ABOX_GATE_FAILED job=$SLURM_JOB_ID"
  exit 1
fi
echo "EL_ABOX_GATE_COMPLETE job=$SLURM_JOB_ID"
