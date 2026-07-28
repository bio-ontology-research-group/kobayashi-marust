#!/bin/bash
#SBATCH --job-name=km-auto-panel-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=08:00:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/auto-panel-20260728/slurm-%x-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/auto-panel-20260728
source_archive=$root/source.tar.gz
source_root=$root/build/source
build_root=$root/build
revision=847a872a13e0d617c950ff5121d44ac89632b174
source_archive_sha=f8d15ab7ed468c8225b208563de03bff87323c428ea3eaed555e97c2f9a9d19d

echo "$source_archive_sha  $source_archive" | /usr/bin/sha256sum -c -
[[ ! -e $build_root ]] || { echo "refusing pre-existing build root" >&2; exit 2; }
/usr/bin/mkdir -p "$source_root" "$build_root/bin" "$build_root/target"
/usr/bin/tar -xzf "$source_archive" -C "$source_root"

export CARGO_TARGET_DIR=$build_root/target
export RUSTFLAGS=-Ctarget-cpu=native
export CARGO_INCREMENTAL=0
cd "$source_root/engine"
/usr/bin/nice -n 5 /home/hohndor/.cargo/bin/cargo build --release --bin km
/usr/bin/install -m 0750 "$CARGO_TARGET_DIR/release/km" "$build_root/bin/km-main"

# The six-arm orchestrator retains generic adapter checks even though this
# contract contains neither RustDL nor Sequoia. Reuse their frozen binaries and
# the already-compiled HermiT full-IRI oracle from the verified 2026-07-22 panel.
old=/ibex/scratch/hohndor/km/full-panel-20260722/build
/usr/bin/install -m 0750 "$old/bin/rustdl" "$build_root/bin/rustdl"
/usr/bin/install -m 0750 "$old/bin/sequoia" "$build_root/bin/sequoia"
/usr/bin/install -m 0640 "$old/sequoia-files.sha256" "$build_root/sequoia-files.sha256"
/usr/bin/install -m 0640 "$old/bin/FullIriHermitOracle.class" "$build_root/bin/FullIriHermitOracle.class"

/usr/bin/python3 - "$build_root" "$revision" <<'PY'
import hashlib
import json
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
binary = root / "bin/km-main"
receipt = {
    "schema_version": 1,
    "source_revision": sys.argv[2],
    "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
    "slurm_job_id": __import__("os").environ["SLURM_JOB_ID"],
}
(root / "build-receipt.json").write_text(
    json.dumps(receipt, sort_keys=True, indent=2) + "\n", encoding="utf-8"
)
PY

"$build_root/bin/km-main" routes >"$build_root/routes.txt"
/usr/bin/awk -F '\t' '$1 == "auto" { found=1 } END { exit !found }' "$build_root/routes.txt"
/usr/bin/awk -F '\t' '$1 == "auto-speed" { found=1 } END { exit !found }' "$build_root/routes.txt"
/usr/bin/awk -F '\t' '$1 == "auto-memory" { found=1 } END { exit !found }' "$build_root/routes.txt"
echo "BUILD_COMPLETE revision=$revision binary=$build_root/bin/km-main"
