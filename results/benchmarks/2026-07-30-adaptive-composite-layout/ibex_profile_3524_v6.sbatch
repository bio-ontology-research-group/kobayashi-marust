#!/bin/bash
# Capture the authoritative current source profile used by automatic routing.
#SBATCH --job-name=km-v6-profile-3524
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v6-20260731/profile-3524/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v6-20260731
out=$root/profile-3524
/usr/bin/mkdir -p "$out"
timeout 600 /usr/bin/prlimit --as=25769803776 -- \
  "$root/km" profile /ibex/scratch/hohndor/km/corpus/ore_ont_3524.owl \
  > "$out/ore_ont_3524.owl.json.tmp"
/usr/bin/python3 - "$out/ore_ont_3524.owl.json.tmp" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != "ore_ont_3524.owl" or row.get("status") != "ok":
    raise SystemExit(f"invalid profile row: {row}")
if not row.get("selected_route"):
    raise SystemExit(f"missing selected route: {row}")
PY
/usr/bin/mv "$out/ore_ont_3524.owl.json.tmp" \
  "$out/ore_ont_3524.owl.json"
echo "PROFILE_COMPLETE ontology=ore_ont_3524.owl"
