#!/bin/bash
# Phase and rule-volume profile for the v0.2.11 exact EL route on ORE8737.
#SBATCH --job-name=km-8737-el-profile
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813/8737-profile/slurm-%j.out

set -u
root=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813
out=$root/8737-profile
expected=$(cut -d' ' -f1 "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected" ]] || exit 2
mkdir -p "$out"
work=${SLURM_TMPDIR:-/tmp}/km-8737-profile-$SLURM_JOB_ID
mkdir -p "$work"
set +e
/usr/bin/time -v -o "$out/ofn.time" "$root/km" ofn \
  /ibex/scratch/hohndor/km/corpus/ore_ont_8737.owl --meta "$work/meta.json" \
  > "$work/clauses.json" 2> "$out/ofn.stderr"
ofn_rc=$?
/usr/bin/time -v -o "$out/elc.time" env -i PATH=/usr/bin:/bin LC_ALL=C \
  KM_ELC_PROFILE=1 "$root/km" elc < "$work/clauses.json" \
  > "$out/elc.json.tmp" 2> "$out/elc.stderr"
elc_rc=$?
set -e
python3 - "$out/result.json.tmp" "$ofn_rc" "$elc_rc" "$expected" <<'PY'
import json,sys
p,ofn,elc,binary=sys.argv[1:]
json.dump({"status":"diagnostic","ofn_rc":int(ofn),"elc_rc":int(elc),
           "binary_sha256":binary},open(p,'w'),sort_keys=True)
open(p,'a').write("\n")
PY
mv "$out/result.json.tmp" "$out/result.json"
echo PROFILE_COMPLETE
