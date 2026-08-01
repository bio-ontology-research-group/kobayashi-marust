#!/bin/bash
#SBATCH --job-name=km-4669-hermit-edges
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=04:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/4669-hermit-edges-%j.out

set -euo pipefail
export LC_ALL=C LANG=C TZ=UTC
root=/ibex/scratch/hohndor/km
run_root=$root/routing_20260715/4669-hermit-edges-${SLURM_JOB_ID}
driver_root=${DRIVER_ROOT:?set DRIVER_ROOT to the deployed immutable inputs}
jdk=$root/bench/jdk8u492-b09
cp_root=$root/bench/hermit_cp
mkdir -p "$run_root/classes"
sha256sum "$driver_root"/* > "$run_root/inputs.sha256"
"$jdk/bin/javac" -cp "$cp_root/*" -d "$run_root/classes" \
    "$driver_root/HermitBatchEntailment4669.java"
/usr/bin/time -v -o "$run_root/time.txt" \
    timeout -k 30 14000 \
    "$jdk/bin/java" -Xmx56g -cp "$run_root/classes:$cp_root/*" \
    HermitBatchEntailment4669 \
    "$driver_root/ore_ont_4669-positive-projection.ofn" \
    "$driver_root/konclude-only-pairs.tsv" \
    > "$run_root/results.jsonl" 2> "$run_root/stderr.txt"
python3 - "$run_root/results.jsonl" <<'PY'
import json, sys
rows = [json.loads(line) for line in open(sys.argv[1]) if line.strip()]
assert len(rows) == 54, len(rows)
assert [row["index"] for row in rows] == list(range(54))
assert all(row["entailed"] != row["counterexample_satisfiable"] for row in rows)
print({"rows": len(rows), "entailed": sum(row["entailed"] for row in rows)})
PY
sha256sum "$run_root"/results.jsonl "$run_root"/stderr.txt "$run_root"/time.txt \
    > "$run_root/outputs.sha256"
echo "COMPLETE run_root=$run_root"
