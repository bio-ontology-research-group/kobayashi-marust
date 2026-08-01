#!/bin/bash
# Recover collision-safe evidence from preserved 3524/15703 classifier outputs.
# One output is fingerprinted per task so the Python closure cannot take down
# the per-ontology panel supervisor or erase evidence for sibling routes.
#SBATCH --job-name=km-v020-fulliri-recover
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=32G
#SBATCH --array=0-26%4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/release-v020-uniform-20260801/recovery/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/release-v020-uniform-20260801
recovery=$root/recovery
drivers=$root/drivers
expected=090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a
/usr/bin/mkdir -p "$recovery/results" "$recovery/fingerprints"

mapfile -t outputs < <(/usr/bin/find \
  "$root/work/49773081" "$root/work/49773083" \
  -type f -name '*.stdout' -size +0c | /usr/bin/sort)
[[ ${#outputs[@]} -eq 27 ]] || {
  echo "expected 27 nonempty preserved outputs, found ${#outputs[@]}" >&2
  exit 2
}
input=${outputs[$SLURM_ARRAY_TASK_ID]}
base=$(/usr/bin/basename "$input" .stdout)
arm=${base%%__*}
ont=${base#*__}
source=/ibex/scratch/hohndor/km/corpus/$ont
prefix=$recovery/fingerprints/${ont%.owl}__$arm
tmp=$recovery/results/${ont%.owl}__$arm.json.tmp
final=${tmp%.tmp}

/usr/bin/python3 "$drivers/full_panel_fingerprint.py" \
  --input "$input" \
  --format json \
  --source-ontology "$source" \
  --output-prefix "$prefix" \
  > "$tmp.fingerprint"

/usr/bin/python3 - \
  "$input" "$prefix.json" "$expected" "$arm" "$ont" "$SLURM_ARRAY_TASK_ID" \
  > "$tmp" <<'PY'
import hashlib
import json
import pathlib
import sys

input_path, fingerprint_path, expected, arm, ont, task = sys.argv[1:]
fingerprint = json.load(open(fingerprint_path, encoding="utf-8"))
digest = hashlib.sha256()
with open(input_path, "rb") as handle:
    for block in iter(lambda: handle.read(1 << 20), b""):
        digest.update(block)
time_path = pathlib.Path(input_path).with_suffix(".time")
wall_s = None
peak_mb = None
if time_path.exists():
    for line in time_path.read_text(errors="replace").splitlines():
        if "Elapsed (wall clock) time" in line:
            value = line.rsplit(": ", 1)[-1]
            parts = value.split(":")
            wall_s = sum(float(part) * 60 ** i for i, part in enumerate(reversed(parts)))
        elif "Maximum resident set size" in line:
            peak_mb = int(line.rsplit(":", 1)[-1].strip()) / 1024
row = {
    "schema_version": 1,
    "status": "ok" if fingerprint["taxonomy_sha256"] == expected else "mismatch",
    "ont": ont,
    "arm": arm,
    "task": int(task),
    "input": input_path,
    "input_sha256": digest.hexdigest(),
    "input_bytes": pathlib.Path(input_path).stat().st_size,
    "wall_s": wall_s,
    "direct_peak_mb": peak_mb,
    "taxonomy_sha256": fingerprint["taxonomy_sha256"],
    "expected_taxonomy_sha256": expected,
    "subsumptions": fingerprint["subsumptions"],
    "unsatisfiable": fingerprint["unsatisfiable"],
    "fingerprint_record": fingerprint_path,
}
print(json.dumps(row, sort_keys=True))
if row["status"] != "ok":
    raise SystemExit(3)
PY

/usr/bin/mv "$tmp" "$final"
echo "FULLIRI_RECOVERY_COMPLETE ontology=$ont arm=$arm"
