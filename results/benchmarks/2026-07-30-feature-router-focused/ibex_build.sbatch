#!/bin/bash
# Source-bound IBEX build for the focused router candidate.
#SBATCH --job-name=km-router-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/router-20260730-v2/slurm-%x-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/router-20260730-v2
revision=7aed67656d3d4084f3b233a07ea4d861f2a58085
tmp_root=${SLURM_TMPDIR:-$root/tmp}/km-router-build-$SLURM_JOB_ID
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$tmp_root/target
export CARGO_TERM_COLOR=never
export CARGO_NET_GIT_FETCH_WITH_CLI=true
mkdir -p "$tmp_root" "$root/build"

/usr/bin/git clone --quiet \
  https://github.com/bio-ontology-research-group/kobayashi-marust.git \
  "$tmp_root/src"
/usr/bin/git -C "$tmp_root/src" checkout --quiet --detach "$revision"
/usr/bin/git -C "$tmp_root/src" apply "$root/router.patch"
(cd "$tmp_root/src/engine" &&
  /usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 32)
/usr/bin/install -m 0555 "$CARGO_TARGET_DIR/release/km" "$root/km.ibex"

/usr/bin/python3 - "$root" "$revision" "$SLURM_JOB_ID" <<'PY'
import hashlib
import json
import pathlib
import subprocess
import sys

root = pathlib.Path(sys.argv[1])
revision = sys.argv[2]
job = sys.argv[3]

def sha(path):
    digest = hashlib.sha256()
    with pathlib.Path(path).open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()

receipt = {
    "schema_version": 1,
    "slurm_job_id": job,
    "base_revision": revision,
    "patch_sha256": sha(root / "router.patch"),
    "binary_sha256": sha(root / "km.ibex"),
    "toolchain": {
        "cargo": subprocess.check_output(
            ["/home/hohndor/.cargo/bin/cargo", "--version"], text=True
        ).strip(),
        "rustc": subprocess.check_output(
            ["/home/hohndor/.cargo/bin/rustc", "--version", "--verbose"], text=True
        ).strip(),
    },
}
(root / "build-receipt.json").write_text(
    json.dumps(receipt, indent=2, sort_keys=True) + "\n"
)
PY

/usr/bin/mv "$root/km.ibex" "$root/km"
echo "BUILD_COMPLETE revision=$revision job=$SLURM_JOB_ID"
