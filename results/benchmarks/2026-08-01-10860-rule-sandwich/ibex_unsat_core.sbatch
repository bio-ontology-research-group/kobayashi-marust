#!/bin/bash
#SBATCH --job-name=km-10860-core
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/10860-rule-sandwich/core-slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715/10860-rule-sandwich
ont=$root/ore_ont_10860_unsat_core.ofn
out=$root/core-results
mkdir -p "$out"

if [ "$SLURM_ARRAY_TASK_ID" = 0 ]; then
  /usr/bin/python3 /ibex/scratch/hohndor/km/harness/ore_runone.py \
    --reasoner konclude --ont "$ont" --outdir "$out" \
    --timeout 600 --memcap-mb 7500 > "$out/konclude.json"
  test "$(/usr/bin/python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["consistent"])' "$out/konclude.json")" = False
else
  cp=/ibex/scratch/hohndor/km/bench/hermit_cp/'*'
  classes=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718/classes
  java=/ibex/scratch/hohndor/km/bench/jdk8u492-b09/bin/java
  "$java" -Xmx6g -cp "$classes:$cp" SatisfiabilityOracle "$ont" urn:km:Situation \
    > "$out/hermit.json" 2> "$out/hermit.err"
  test "$(/usr/bin/python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["satisfiable"])' "$out/hermit.json")" = False
fi
