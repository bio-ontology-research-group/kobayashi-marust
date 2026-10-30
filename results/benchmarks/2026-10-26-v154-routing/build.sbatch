#!/bin/bash
# Build the hash-pinned v1.5.4 routing candidate on an IBEX compute node.
#SBATCH --job-name=km154-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v154-routing-20261026/slurm/build-%j.out
set -euo pipefail
ROOT=/ibex/scratch/projects/c2014/hohndor/km/v154-routing-20261026
build=${SLURM_TMPDIR:-/tmp}/km154-build
/usr/bin/rm -rf "$build"; /usr/bin/mkdir -p "$build/src"
/usr/bin/tar -xzf "$ROOT/source.tar.gz" -C "$build/src"
cd "$build/src/engine"
CARGO_TARGET_DIR="$build/target" nice cargo build --release --bin km
"$build/target/release/km" routes | /usr/bin/grep -q '^auto'
/usr/bin/install -m 755 "$build/target/release/km" "$ROOT/km"
/usr/bin/sha256sum "$ROOT/km" > "$ROOT/km.sha256"
echo "BUILD_OK $(/usr/bin/cut -d' ' -f1 < "$ROOT/km.sha256") $(/usr/bin/hostname)"
# Harness inventory for the paired measurement: the v1.5.3 release flags,
# unchanged, and the hash-pinned candidate binary.
/usr/bin/python3 - "$ROOT" <<'PY'
import json, sys, hashlib
root = sys.argv[1]
sha = open(root + '/km.sha256').read().split()[0]
flags = json.load(open('/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/recovery-v153-scoped-20261025/combined-artifact.json'))['flags']
json.dump({'artifacts': [{'id': 'km', 'version': 'v1.5.4-routing-candidate', 'path': root + '/km', 'sha256': sha}],
           'flags': flags}, open(root + '/inventory.json', 'w'), indent=2)
PY
