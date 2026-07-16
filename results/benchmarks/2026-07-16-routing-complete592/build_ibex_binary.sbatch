#!/bin/bash
# Build the exact checked-out source on an IBEX compute node, then run startup
# and one real classification smoke test before publishing the binary.
#SBATCH --job-name=km-proof-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/route_proof_20260716/slurm/build-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
proof_root=$km_root/route_proof_20260716
source_archive=$proof_root/source.tar.gz
build_root=${SLURM_TMPDIR:-/tmp}/km-proof-build
source_root=$build_root/source
target_root=$build_root/target
candidate=$target_root/release/km
published=$proof_root/km
smoke_ontology=$km_root/corpus/ore_ont_33.owl
smoke_output=$build_root/smoke.json

rm -rf "$build_root"
mkdir -p "$source_root" "$target_root"
tar -xzf "$source_archive" -C "$source_root"

cd "$source_root/engine"
CARGO_TARGET_DIR="$target_root" nice cargo build --release --bin km

"$candidate" routes > "$build_root/routes.txt"
grep -q '^production_all' "$build_root/routes.txt"

env KM_ROUTE=elc timeout -k 5 120 "$candidate" classify "$smoke_ontology" \
  > "$smoke_output"
python3 - "$smoke_output" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as handle:
    data = json.load(handle)
for field in ("consistent", "subsumptions"):
    if field not in data:
        raise SystemExit(f"smoke result missing {field}")
PY

install -m 755 "$candidate" "$published.tmp"
mv -f "$published.tmp" "$published"
sha256sum "$published" > "$proof_root/km.sha256"
printf 'BUILD_OK binary=%s smoke=%s host=%s\n' \
  "$(cut -d' ' -f1 < "$proof_root/km.sha256")" \
  "$(sha256sum "$smoke_output" | cut -d' ' -f1)" "$(hostname)"
