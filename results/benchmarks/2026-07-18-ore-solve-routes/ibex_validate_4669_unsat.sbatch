#!/bin/bash
# Independently adjudicate the 56 classes on which the 4669 routes disagree.
#SBATCH --job-name=km-4669-sat
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --array=0-55%8
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718/slurm/sat4669-%A_%a.out

set -u

km_root=/ibex/scratch/hohndor/km
validation=$km_root/routing_20260715/tail-validation-20260718
classes=$validation/classes
queries=${KM_QUERY_FILE:-$validation/ore_ont_4669-ht-only-unsat.txt}
ontology=${KM_ONTOLOGY:-$km_root/corpus/ore_ont_4669.owl}
java=$km_root/bench/jdk8u492-b09/bin/java
classpath=$classes:$km_root/bench/hermit_cp/'*'
index=${SLURM_ARRAY_TASK_ID:-0}
query=$(/usr/bin/sed -n "$((index + 1))p" "$queries")
out=${KM_QUERY_OUTPUT:-$validation/4669-satisfiability}

/usr/bin/mkdir -p "$out"
stdout=$out/$index.stdout.json
stderr=$out/$index.stderr
timing=$out/$index.time

/usr/bin/timeout -k 10 240 /usr/bin/time -v -o "$timing" \
  "$java" -Xmx16g -cp "$classpath" SatisfiabilityOracle "$ontology" "$query" \
  > "$stdout" 2> "$stderr"
rc=$?

/usr/bin/python3 - "$index" "$query" "$rc" "$stdout" "$stderr" "$timing" <<'PY'
import hashlib
import json
from pathlib import Path
import re
import sys

index, query, rc, stdout, stderr, timing = sys.argv[1:]
rc = int(rc)
stdout_path, stderr_path, timing_path = map(Path, (stdout, stderr, timing))
status = "ok" if rc == 0 else "timeout" if rc == 124 else "error"
answer = None
if stdout_path.exists() and stdout_path.stat().st_size:
    try:
        answer = json.loads(stdout_path.read_text())
    except ValueError:
        status = "invalid_output"
peak_mb = None
if timing_path.exists():
    match = re.search(
        r"Maximum resident set size \(kbytes\):\s*(\d+)",
        timing_path.read_text(errors="replace"),
    )
    if match:
        peak_mb = round(int(match.group(1)) / 1024, 2)
record = {
    "schema_version": 1,
    "index": int(index),
    "class": query,
    "status": status,
    "return_code": rc,
    "satisfiable": answer.get("satisfiable") if answer else None,
    "peak_mb": peak_mb,
    "slurm_job_id": __import__("os").environ.get("SLURM_JOB_ID"),
    "slurm_array_job_id": __import__("os").environ.get("SLURM_ARRAY_JOB_ID"),
    "slurm_array_task_id": __import__("os").environ.get("SLURM_ARRAY_TASK_ID"),
    "stdout_sha256": hashlib.sha256(stdout_path.read_bytes()).hexdigest()
        if stdout_path.exists() else None,
    "stderr_tail": stderr_path.read_text(errors="replace")[-2000:]
        if stderr_path.exists() else "",
}
result = stdout_path.with_suffix(".validation.json")
tmp = result.with_suffix(result.suffix + ".tmp")
tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
tmp.replace(result)
print(json.dumps(record, sort_keys=True))
PY

/usr/bin/printf 'DONE index=%s class=%s rc=%s host=%s\n' \
  "$index" "$query" "$rc" "$(hostname)"
exit 0
