#!/bin/bash
# Build amended candidate 9047217 on an IBEX compute node for its older glibc ABI.
# The input is a deterministic git archive of the exact local commit.
#SBATCH --job-name=km-9047217-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/target-f40713c/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "candidate build failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR
[[ $# -eq 0 ]]

export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export LC_ALL=C
export CARGO_TERM_COLOR=never
root=/ibex/scratch/hohndor/km/target-f40713c
archive=$root/source/km-9047217-source.tar.gz
archive_sha=4a476a7f6ef8aa4ccf649c1aba3b1caf277095dc0ede8387ac3cd568b3c33d79
revision=9047217be11e42f8e322cc098bc8362203b34804
work=${SLURM_TMPDIR:-$root/work}/build-$SLURM_JOB_ID
target=$work/target
binary=$root/bin/km-9047217-ibex
receipt=$root/bin/km-9047217-ibex.receipt.json

[[ ! -e $binary && ! -e $receipt ]]
actual_archive_sha=$(/usr/bin/sha256sum "$archive" | /usr/bin/awk '{print $1}')
/usr/bin/printf 'SOURCE_ARCHIVE expected=%s actual=%s path=%s\n' \
    "$archive_sha" "$actual_archive_sha" "$archive"
[[ $actual_archive_sha == "$archive_sha" ]]
/usr/bin/mkdir -p "$work" "$target"
/usr/bin/tar -xzf "$archive" -C "$work"
export CARGO_TARGET_DIR=$target
(
    cd "$work/source/engine"
    /usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16
)
/usr/bin/install -m 0555 "$target/release/km" "$binary"

/usr/bin/python3 - "$binary" "$receipt" "$archive" "$archive_sha" "$revision" \
    "$SLURM_JOB_ID" <<'PY'
import hashlib
import json
from pathlib import Path
import subprocess
import sys

binary, receipt, archive, archive_sha, revision, job = sys.argv[1:]
binary = Path(binary)
record = {
    "schema_version": 1,
    "source_revision": revision,
    "source_archive": archive,
    "source_archive_sha256": archive_sha,
    "binary": str(binary),
    "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
    "build_command": ["cargo", "build", "--release", "--locked", "--bin", "km", "--jobs", "16"],
    "cargo_version": subprocess.check_output(["cargo", "--version"], text=True).strip(),
    "rustc_version": subprocess.check_output(["rustc", "--version", "--verbose"], text=True).strip(),
    "slurm_job_id": job,
}
Path(receipt).write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
print(json.dumps(record, sort_keys=True))
PY
/usr/bin/sha256sum "$archive" "$binary" "$receipt"
/usr/bin/printf 'CANDIDATE_BUILD_COMPLETE revision=%s binary=%s\n' "$revision" "$binary"
