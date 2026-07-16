#!/bin/bash
# Build a hash-pinned KM source archive on an IBEX compute node. PROOF_ROOT
# must contain source.tar.gz. The binary is published only after route and
# real-classification smoke checks pass.
#SBATCH --job-name=km-integrated-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/integrated-build-%j.out

set -euo pipefail

: "${PROOF_ROOT:?submit with --export=ALL,PROOF_ROOT=/absolute/path}"
source_archive=$PROOF_ROOT/source.tar.gz
build_root=${SLURM_TMPDIR:-/tmp}/km-integrated-build
source_root=$build_root/source
target_root=$build_root/target
candidate=$target_root/release/km
published=$PROOF_ROOT/km
smoke_ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_33.owl
smoke_output=$build_root/smoke.json

/usr/bin/rm -rf "$build_root"
/usr/bin/mkdir -p "$source_root" "$target_root" "$PROOF_ROOT"
/usr/bin/tar -xzf "$source_archive" -C "$source_root"

cd "$source_root/engine"
CARGO_TARGET_DIR="$target_root" nice cargo build --release --bin km

"$candidate" routes > "$build_root/routes.txt"
/usr/bin/grep -q '^production_all' "$build_root/routes.txt"

/usr/bin/env KM_ROUTE=production_all /usr/bin/timeout -k 5 120 \
  "$candidate" classify "$smoke_ontology" > "$smoke_output"
/usr/bin/python3 - "$smoke_output" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as handle:
    data = json.load(handle)
for field in ("consistent", "subsumptions"):
    if field not in data:
        raise SystemExit(f"smoke result missing {field}")
PY

/usr/bin/install -m 755 "$candidate" "$published.tmp"
/usr/bin/mv -f "$published.tmp" "$published"
/usr/bin/sha256sum "$published" > "$PROOF_ROOT/km.sha256"
/usr/bin/printf 'BUILD_OK binary=%s smoke=%s host=%s\n' \
  "$(/usr/bin/cut -d' ' -f1 < "$PROOF_ROOT/km.sha256")" \
  "$(/usr/bin/sha256sum "$smoke_output" | /usr/bin/cut -d' ' -f1)" \
  "$(/usr/bin/hostname)"
