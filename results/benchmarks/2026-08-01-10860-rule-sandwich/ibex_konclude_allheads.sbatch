#!/bin/bash
#SBATCH --job-name=km-10860-sandwich
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/10860-rule-sandwich/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/routing_20260715/10860-rule-sandwich
runner=/ibex/scratch/hohndor/km/harness/ore_runone.py
ont=$root/ore_ont_10860_allheads.owl
out=$root/results
mkdir -p "$out"

/usr/bin/python3 "$runner" \
  --reasoner konclude \
  --ont "$ont" \
  --outdir "$out" \
  --timeout 1200 \
  --memcap-mb 15000 \
  > "$out/konclude__ore_ont_10860_allheads.owl.json"

test -s "$out/konclude__ore_ont_10860_allheads.owl.json"
/usr/bin/python3 - "$out/konclude__ore_ont_10860_allheads.owl.json" <<'PY'
import json
import sys

result = json.load(open(sys.argv[1], encoding="utf-8"))
assert result["status"] == "ok", result
assert result["consistent"] is True, result
assert result["sig_sha"], result
print(json.dumps(result, sort_keys=True))
PY
