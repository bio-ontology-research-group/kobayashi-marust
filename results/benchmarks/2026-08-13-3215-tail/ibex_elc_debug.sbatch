#!/bin/bash
# Diagnose why the exact certified-EL route declines ORE3215.
# Diagnostic only: a nonzero ELC result is not benchmark acceptance evidence.
#SBATCH --job-name=km-3215-elc-debug
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813/3215-elc-debug-%j.out

set -u
root=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813
out="$root/3215-elc-debug"
bin="$root/km"
ont=/ibex/scratch/hohndor/km/corpus/ore_ont_3215.owl
expected=$(cut -d' ' -f1 "$root/km.sha256")
[[ $(sha256sum "$bin" | cut -d' ' -f1) == "$expected" ]] || exit 2
mkdir -p "$out"
work=${SLURM_TMPDIR:-/tmp}/km-3215-elc-debug-$SLURM_JOB_ID
mkdir -p "$work"

set +e
/usr/bin/time -v -o "$out/ofn.time" timeout -k 10 120 \
  env -i PATH=/usr/bin:/bin LC_ALL=C "$bin" ofn "$ont" \
  --meta "$work/meta.json" > "$work/clauses.json" 2> "$out/ofn.stderr"
ofn_rc=$?
if [[ $ofn_rc -eq 0 ]]; then
  /usr/bin/time -v -o "$out/elc.time" timeout -k 10 180 \
    env -i PATH=/usr/bin:/bin LC_ALL=C KM_ELC_CERT=2 KM_ELC_DEBUG=1 \
      KM_ELC_PROFILE=1 "$bin" elc \
    < "$work/clauses.json" > "$out/elc.json.tmp" 2> "$out/elc.stderr"
  elc_rc=$?
else
  elc_rc=99
fi
set -e

python3 - "$out/result.json.tmp" "$ofn_rc" "$elc_rc" "$expected" "$work/clauses.json" <<'PY'
import hashlib,json,os,sys
p,ofn,elc,binary,clauses=sys.argv[1:]
sha=lambda q: hashlib.sha256(open(q,'rb').read()).hexdigest() if os.path.exists(q) else None
json.dump({"status":"diagnostic","ofn_rc":int(ofn),"elc_rc":int(elc),
           "binary_sha256":binary,"clauses_sha256":sha(clauses)},open(p,'w'),sort_keys=True)
open(p,'a').write("\n")
PY
mv "$out/result.json.tmp" "$out/result.json"
rm -f "$out/elc.json.tmp"
echo DIAGNOSTIC_COMPLETE
