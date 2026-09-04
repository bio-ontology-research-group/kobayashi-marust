#!/bin/bash
#SBATCH --job-name=km-v14-guarded-tin
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:02:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-uberon-guarded-20260904/tin-%j.out
set -euo pipefail

root=/ibex/scratch/hohndor/km/v14-uberon-guarded-20260904
binary=$root/km-guarded
expected=c9be93d3c3c0701a175658c8ba935db0a29df420493e8ed7c1b32f85f5eb2805
tin=/ibex/scratch/hohndor/km/v14-uberon-rules-tin-v2-20260904/uberon.tin.json
tin_expected=01dca21c579745be5e8e5eca9d8b752d7811070a69475f73441b9150ae0853c6
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
[[ $(sha256sum "$tin" | cut -d' ' -f1) == "$tin_expected" ]]
/usr/bin/time -v -o "$root/tin.time" \
  /usr/bin/timeout -k 5 90 /usr/bin/env \
  KM_RULES_CONSISTENCY=1 KM_TAB_CAREFUL_INC=1 KM_TAB_CAREFUL_ORDER=1 \
  KM_TAB_CAREFUL_LAZY=1 "$binary" tableau < "$tin" \
  > "$root/tin.output.json" 2> "$root/tin.stderr"
python3 - "$root/tin.output.json" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r == {"consistent": True, "unsatisfiable": [], "subsumptions": []}, r
PY
[[ $(sha256sum "$root/tin.output.json" | cut -d' ' -f1) == d9e29cb6ed8c1a516ae4cbdf8d17f70d518fbe789860e365cdb3d5f26b52a6b4 ]]
{
  printf 'binary_sha256\t%s\n' "$expected"
  printf 'tinput_sha256\t%s\n' "$tin_expected"
  printf 'output_sha256\t%s\n' "$(sha256sum "$root/tin.output.json" | cut -d' ' -f1)"
  grep -E 'Elapsed \(wall clock\) time|Maximum resident set size' "$root/tin.time"
  printf 'slurm_job_id\t%s\nhost\t%s\n' "$SLURM_JOB_ID" "$(hostname)"
} > "$root/tin-receipt.tsv"
echo GUARDED_TIN_COMPLETE
