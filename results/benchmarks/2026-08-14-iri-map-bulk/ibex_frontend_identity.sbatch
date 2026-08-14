#!/bin/bash
#SBATCH --job-name=km-iri-frontend-id
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --array=0-591%40
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/declaration-seed-20260814/frontend-identity/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/declaration-seed-20260814/frontend-identity
baseline=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814/km
candidate=/ibex/scratch/hohndor/km/declaration-seed-20260814/km
baseline_sha=b51af8f49e59f4c74515bb2677e68706a585a2d851ae838275046a81b77fe965
candidate_sha=7c090417f169d5ee60992f5203e2fe62aee4e8244b50e1aadf7a03b08bf1a71a
list=$root/ore592.txt
index=${SLURM_ARRAY_TASK_ID:?}
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == "$candidate_sha" ]]
[[ $(wc -l < "$list") -eq 592 ]]
ontology=$(sed -n "$((index + 1))p" "$list")
[[ $ontology =~ ^ore_ont_[0-9]+\.owl$ ]]
mkdir -p "$root/results"
out=$root/results/$ontology.json
if [[ -s $out ]] && /usr/bin/python3 - "$out" "$ontology" "$index" "$candidate_sha" <<'PY'
import json,sys
x=json.load(open(sys.argv[1]))
assert x["ontology"]==sys.argv[2] and x["index"]==int(sys.argv[3])
assert x["candidate_binary_sha256"]==sys.argv[4] and x["identical"] is True
PY
then
  echo "ALREADY_COMPLETE index=$index ontology=$ontology"
  exit 0
fi
work=${SLURM_TMPDIR:-/tmp}/km-iri-frontend-${SLURM_JOB_ID}
mkdir -p "$work"
declare -A clause_sha meta_sha
for label in baseline candidate; do
  binary=$baseline
  [[ $label == candidate ]] && binary=$candidate
  meta=$work/$label.meta.json
  clause_sha[$label]=$(timeout 240 /usr/bin/prlimit --as=25769803776 -- \
    "$binary" ofn "/ibex/scratch/hohndor/km/corpus/$ontology" --meta "$meta" \
    | sha256sum | cut -d' ' -f1)
  [[ -s $meta ]]
  meta_sha[$label]=$(sha256sum "$meta" | cut -d' ' -f1)
done
identical=false
if [[ ${clause_sha[baseline]} == ${clause_sha[candidate]} \
   && ${meta_sha[baseline]} == ${meta_sha[candidate]} ]]; then
  identical=true
fi
/usr/bin/python3 - "$ontology" "$index" "$baseline_sha" "$candidate_sha" \
  "${clause_sha[baseline]}" "${clause_sha[candidate]}" \
  "${meta_sha[baseline]}" "${meta_sha[candidate]}" "$identical" > "$out.tmp" <<'PY'
import json,sys
print(json.dumps({
  "ontology":sys.argv[1], "index":int(sys.argv[2]),
  "baseline_binary_sha256":sys.argv[3], "candidate_binary_sha256":sys.argv[4],
  "baseline_clauses_sha256":sys.argv[5], "candidate_clauses_sha256":sys.argv[6],
  "baseline_meta_sha256":sys.argv[7], "candidate_meta_sha256":sys.argv[8],
  "identical":sys.argv[9]=="true",
},sort_keys=True))
PY
mv "$out.tmp" "$out"
[[ $identical == true ]]
echo "TASK_COMPLETE index=$index ontology=$ontology"
