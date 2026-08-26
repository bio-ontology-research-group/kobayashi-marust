#!/bin/bash
#SBATCH --job-name=km-empty-query-unsat
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=4G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-empty-query-v8-20260825/inconsistent-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-empty-query-v8-20260825
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
input=${SLURM_TMPDIR:-/tmp}/inconsistent-abox.ofn
output=$root/inconsistent-abox.json
fixture_sha=1188d698e28993b07dbcea2d9bdabed1ce1b941195d610746b199008802d4e08
[[ -s "$root/inconsistent-abox.ofn" ]]
[[ $(sha256sum "$root/inconsistent-abox.ofn" | cut -d' ' -f1) == "$fixture_sha" ]]
cp "$root/inconsistent-abox.ofn" "$input"
trace=$root/inconsistent-abox.trace
env KM_ROUTE=auto KM_ABOX_DISJOINT_UNION_CHECK=1 KM_DISJOINT_UNION_TRACE=1 \
  "$root/km" classify "$input" > "$output.tmp" 2> "$trace.tmp"
grep -qx 'KM_DISJOINT_UNION result=inconsistent' "$trace.tmp"
/usr/bin/python3 - "$output.tmp" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r.get("consistent") is False, {
    "consistent": r.get("consistent"),
    "dropped": r.get("dropped"),
    "subsumptions": len(r.get("subsumptions", [])),
}
assert r.get("dropped") == 0, r.get("dropped")
PY
mv "$output.tmp" "$output"
mv "$trace.tmp" "$trace"
echo INCONSISTENT_ABOX_GATE_COMPLETE
