#!/bin/bash
#SBATCH --job-name=km-profile-all
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --array=0-29
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=24G
#SBATCH --time=01:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813/profile-all/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
binary=$root/km
expected_binary=1abb488945d16df5ba16ee6aa261b1a2aac356b2bfe183b256856c7e28fe9734
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected_binary" ]]
corpus=/ibex/scratch/hohndor/km/corpus
out_root=$root/profile-all
mkdir -p "$out_root/results" "$out_root/checkpoints"

list=$root/ore592.txt
[[ $(sha256sum "$list" | cut -d' ' -f1) == 7849b4b875d3b9bc5e214b67a1fa584f3d684e595954ca11a816448c87d3d2b8 ]]
mapfile -t ontologies < "$list"
[[ ${#ontologies[@]} -eq 592 ]]
[[ $(printf '%s\n' "${ontologies[@]}" | sort -u | wc -l) -eq 592 ]]

tmp="$out_root/results/task-${SLURM_ARRAY_TASK_ID}.jsonl.tmp"
: > "$tmp"
processed=0
for ((index=SLURM_ARRAY_TASK_ID; index<${#ontologies[@]}; index+=30)); do
  ontology=${ontologies[$index]}
  one="$out_root/results/task-${SLURM_ARRAY_TASK_ID}-${index}.one.tmp"
  : > "$one"
  "$binary" profile "$corpus/$ontology" > "$one" || true
  if /usr/bin/jq -e . "$one" >/dev/null 2>&1; then
    /usr/bin/jq -c . "$one" >> "$tmp"
  else
    printf '{"ont":"%s","status":"no_output"}\n' "$ontology" >> "$tmp"
  fi
  rm -f "$one"
  processed=$((processed + 1))
done
[[ $(wc -l < "$tmp") -eq $processed ]]
mv "$tmp" "$out_root/results/task-${SLURM_ARRAY_TASK_ID}.jsonl"
printf '{"task":%d,"processed":%d,"binary_sha256":"%s"}\n' \
  "$SLURM_ARRAY_TASK_ID" "$processed" "$expected_binary" \
  > "$out_root/checkpoints/task-${SLURM_ARRAY_TASK_ID}.json.tmp"
mv "$out_root/checkpoints/task-${SLURM_ARRAY_TASK_ID}.json.tmp" \
  "$out_root/checkpoints/task-${SLURM_ARRAY_TASK_ID}.json"
