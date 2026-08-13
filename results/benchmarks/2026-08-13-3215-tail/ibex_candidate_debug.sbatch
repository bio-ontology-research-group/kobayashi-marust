#!/bin/bash
# Certificate trace for the IBEX-built pre-certificate-hoist candidate.
#SBATCH --job-name=km-3215-hoist-debug
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:04:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-3215-precert-hoist-20260813/debug-%j.out

set -u
root=/ibex/scratch/hohndor/km/candidate-3215-precert-hoist-20260813
out=$root/debug
expected=$(cut -d' ' -f1 "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected" ]] || exit 2
mkdir -p "$out"
work=${SLURM_TMPDIR:-/tmp}/km-3215-hoist-debug-$SLURM_JOB_ID
mkdir -p "$work"
set +e
"$root/km" ofn /ibex/scratch/hohndor/km/corpus/ore_ont_3215.owl \
  --meta "$work/meta.json" > "$work/clauses.json" 2> "$out/ofn.stderr"
ofn_rc=$?
env -i PATH=/usr/bin:/bin LC_ALL=C KM_ELC_CERT=2 KM_ELC_DEBUG=1 \
  "$root/km" elc < "$work/clauses.json" > "$out/elc.json.tmp" 2> "$out/elc.stderr"
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
echo DEBUG_COMPLETE
