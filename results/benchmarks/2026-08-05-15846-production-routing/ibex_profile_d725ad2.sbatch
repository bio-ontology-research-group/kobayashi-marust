#!/bin/bash
#SBATCH --job-name=km-d725ad2-profile
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=24G
#SBATCH --array=0-591%20
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-d725ad2-large-abox-20260805/profile-slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-d725ad2-large-abox-20260805
expected_binary=7e0e28e77a0c86d937f814198a0c85ad35ea086c91d5fefa70b5fd0c3dc775b7
[[ $(sha256sum "$root/km" | cut -d" " -f1) == "$expected_binary" ]]
ontology_list=/ibex/scratch/hohndor/km/routing_20260715/onts.txt
index=${SLURM_ARRAY_TASK_ID:?}
(( index < 592 ))
[[ $(wc -l < "$ontology_list") -eq 592 ]]
ontology=$(sed -n "$((index + 1))p" "$ontology_list")
[[ $ontology =~ ^ore_ont_[0-9]+\.owl$ ]]
mkdir -p "$root/profiles" "$root/profile-failures"
output=$root/profiles/$ontology.json
checkpoint=$root/profiles/$ontology.checkpoint.json

if [[ -e "$output" && -e "$checkpoint" ]]; then
  /usr/bin/python3 - "$output" "$checkpoint" "$ontology" "$index" <<'PY'
import json
import sys

profile = json.load(open(sys.argv[1]))
checkpoint = json.load(open(sys.argv[2]))
if profile.get("ont") != sys.argv[3] or profile.get("status") != "ok":
    raise SystemExit("invalid existing profile")
if not profile.get("selected_route"):
    raise SystemExit("existing profile lacks selected route")
if checkpoint != {"index": int(sys.argv[4]), "ont": sys.argv[3], "status": "complete"}:
    raise SystemExit("invalid existing checkpoint")
PY
  echo "ALREADY_COMPLETE index=$index ontology=$ontology"
  exit 0
fi

tmp=$output.tmp
err=$root/profile-failures/$ontology.err.tmp
timeout 240 /usr/bin/prlimit --as=25769803776 -- \
  "$root/km" profile "/ibex/scratch/hohndor/km/corpus/$ontology" > "$tmp" 2> "$err"
/usr/bin/python3 - "$tmp" "$ontology" <<'PY'
import json
import sys

profile = json.load(open(sys.argv[1]))
if profile.get("ont") != sys.argv[2] or profile.get("status") != "ok":
    raise SystemExit("invalid new profile")
if not profile.get("selected_route"):
    raise SystemExit("new profile lacks selected route")
PY
mv "$tmp" "$output"
unlink "$err"
/usr/bin/python3 - "$index" "$ontology" > "$checkpoint.tmp" <<'PY'
import json
import sys
print(json.dumps({"index": int(sys.argv[1]), "ont": sys.argv[2], "status": "complete"}, sort_keys=True))
PY
mv "$checkpoint.tmp" "$checkpoint"
echo "TASK_COMPLETE index=$index ontology=$ontology"
