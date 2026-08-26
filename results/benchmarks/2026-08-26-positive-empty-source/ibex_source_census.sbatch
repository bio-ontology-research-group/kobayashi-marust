#!/bin/bash
#SBATCH --job-name=km-v110-v7-census
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --array=0-591%40
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --cpus-per-task=2
#SBATCH --mem=3G
#SBATCH --time=00:03:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v7-20260826/census/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v7-20260826
corpus=/ibex/scratch/hohndor/km/corpus
ontology_list=/ibex/scratch/hohndor/km/v1-cert-overhead-v6-20260826/full-sweep/ore592.txt
expected_binary=a28b41934ea033f8274b3a71734ea6733a3989d573e8eccd5ca099c08bd344b8
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected_binary" ]]
[[ $(sha256sum "$ontology_list" | cut -d' ' -f1) == \
  7849b4b875d3b9bc5e214b67a1fa584f3d684e595954ca11a816448c87d3d2b8 ]]
mapfile -t inputs < "$ontology_list"
[[ ${#inputs[@]} == 592 ]]
name=${inputs[$SLURM_ARRAY_TASK_ID]}
input=$corpus/$name
[[ -f $input ]]
id=$(basename "$name" .owl)
id=${id#ore_ont_}
result=$root/census/results/${id}.tsv
stderr_result=$root/census/results/${id}.stderr
if [[ -f $result && -f $stderr_result ]] \
    && awk -F '\t' -v id="$id" '
      NR == 1 { ok = ($1 == "ontology" && $2 == "status" && $3 == "exit_code") }
      NR == 2 { ok = ok && $1 == id && ($2 == "accepted" || $2 == "declined") \
        && $3 ~ /^[0-9]+$/ }
      END { exit !(ok && NR == 2) }
    ' "$result"; then
  echo "CENSUS_REUSE ontology=$id"
  exit 0
fi
work=${SLURM_TMPDIR:-/tmp}/km-v110-v7-census-${SLURM_JOB_ID}
mkdir -p "$work" "$root/census/results"
trap 'rm -rf "$work"' EXIT
set +e
timeout -k 1 5 env KM_ROUTE=auto KM_POSITIVE_EMPTY_SOURCE=1 KM_TIMING=1 \
  "$root/km" classify "$input" > "$work/output.json" 2> "$work/stderr"
exit_code=$?
set -e
if grep -q 'route=positive_empty_source' "$work/stderr"; then
  status=accepted
  [[ $exit_code == 0 ]]
else
  status=declined
fi
printf 'ontology\tstatus\texit_code\n%s\t%s\t%s\n' "$id" "$status" "$exit_code" \
  > "$work/result.tsv"
install -m 644 "$work/result.tsv" "$result"
install -m 644 "$work/stderr" "$stderr_result"
echo "CENSUS ontology=$id status=$status exit=$exit_code"
