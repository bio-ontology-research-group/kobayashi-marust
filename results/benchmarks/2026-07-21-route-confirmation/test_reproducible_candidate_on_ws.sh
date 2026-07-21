#!/bin/bash
# Run the complete Rust test suite from an already archived reproducible KM
# build input. The test has no network access and uses at most four cores.

set -euo pipefail

if [[ $(/usr/bin/hostname) != leechuck-office ]]; then
    echo "refusing test: run this only on leechuck-office (ws)" >&2
    exit 2
fi
if [[ $# -ne 2 ]]; then
    echo "usage: $0 CAPSULE_DIRECTORY EMPTY_TEST_RECEIPT_DIRECTORY" >&2
    exit 2
fi

capsule_directory=$(/usr/bin/readlink -f "$1")
receipt_directory=$(/usr/bin/readlink -m "$2")
for input in build-input.tar.gz build-input-files.sha256 build-receipt.json; do
    [[ -s $capsule_directory/$input ]] || {
        echo "missing capsule input: $capsule_directory/$input" >&2
        exit 2
    }
done
if [[ -e $receipt_directory ]]; then
    echo "test receipt directory already exists: $receipt_directory" >&2
    exit 2
fi
if /usr/bin/pgrep -x cargo >/dev/null || /usr/bin/pgrep -x rustc >/dev/null; then
    echo "another Cargo/Rust build is running; serialize tests" >&2
    exit 3
fi

read -r load_one _ </proc/loadavg
available_kib=$(/usr/bin/awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
if /usr/bin/awk -v load="$load_one" 'BEGIN {exit !(load > 8.0)}'; then
    echo "load $load_one exceeds the conservative ws test limit" >&2
    exit 3
fi
if [[ ${available_kib:-0} -lt 33554432 ]]; then
    echo "less than 32 GiB available; refusing test" >&2
    exit 3
fi

image_digest=sha256:646e8ceea789b00c5cfa339816a3ed44940dbf1651dc167b78f3c0aefcae0025
image_ref=rust@${image_digest}
stage_directory=$(/usr/bin/mktemp -d /tmp/km-repro-test.XXXXXX)
cleanup() {
    if [[ $stage_directory == /tmp/km-repro-test.* ]] \
        && [[ -d $stage_directory ]]; then
        set +e
        /usr/bin/docker run --rm -v "$stage_directory:/stage" "$image_ref" \
            /bin/bash -c \
            "chown -R $(/usr/bin/id -u):$(/usr/bin/id -g) /stage" \
            >/dev/null 2>&1
        /usr/bin/rm -rf -- "$stage_directory" >/dev/null 2>&1
    fi
}
trap cleanup EXIT

/usr/bin/mkdir -p "$receipt_directory" "$stage_directory/source" \
    "$stage_directory/target"
/usr/bin/tar -xzf "$capsule_directory/build-input.tar.gz" \
    -C "$stage_directory/source"
(
    cd "$stage_directory/source"
    /usr/bin/sha256sum --check --strict \
        "$capsule_directory/build-input-files.sha256"
) > "$receipt_directory/input-check.log"

set +e
/usr/bin/docker run --rm --network=none --cpus=4 --memory=16g \
    --pids-limit=1024 \
    -e CARGO_TARGET_DIR=/target \
    -e CARGO_BUILD_JOBS=4 \
    -e CARGO_INCREMENTAL=0 \
    -e SOURCE_DATE_EPOCH=0 \
    -v "$stage_directory/source:/src:ro" \
    -v "$stage_directory/target:/target" \
    -w /src/engine "$image_ref" \
    /bin/bash -c \
    'nice -n 10 cargo test --release --locked --offline -j4' \
    > "$receipt_directory/full-tests.log" 2>&1
test_rc=$?
set -e

/usr/bin/install -m 0555 "$0" \
    "$receipt_directory/test_reproducible_candidate_on_ws.sh"
/usr/bin/python3 -I - \
    "$capsule_directory" "$receipt_directory" "$test_rc" \
    "$image_digest" <<'PY'
import hashlib
import json
from pathlib import Path
import re
import sys

capsule, output = map(Path, sys.argv[1:3])
return_code = int(sys.argv[3])
image_digest = sys.argv[4]

def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()

log_path = output / "full-tests.log"
log = log_path.read_text(encoding="utf-8", errors="replace")
summaries = []
pattern = re.compile(
    r"test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; "
    r"(\d+) ignored; (\d+) measured; (\d+) filtered out"
)
for match in pattern.finditer(log):
    summaries.append(
        {
            "status": match.group(1),
            "passed": int(match.group(2)),
            "failed": int(match.group(3)),
            "ignored": int(match.group(4)),
            "measured": int(match.group(5)),
            "filtered_out": int(match.group(6)),
        }
    )
record = {
    "schema_version": 1,
    "status": "verified_full_tests" if return_code == 0 else "tests_failed",
    "return_code": return_code,
    "command": [
        "cargo", "test", "--release", "--locked", "--offline", "-j4"
    ],
    "network_disabled": True,
    "cpus": 4,
    "memory_gib": 16,
    "container_image_digest": image_digest,
    "capsule_build_receipt_sha256": sha(capsule / "build-receipt.json"),
    "capsule_build_input_archive_sha256": sha(capsule / "build-input.tar.gz"),
    "capsule_build_input_manifest_sha256": sha(
        capsule / "build-input-files.sha256"
    ),
    "test_driver_sha256": sha(output / "test_reproducible_candidate_on_ws.sh"),
    "input_check_sha256": sha(output / "input-check.log"),
    "full_tests_sha256": sha(log_path),
    "test_harnesses": len(summaries),
    "passed": sum(row["passed"] for row in summaries),
    "failed": sum(row["failed"] for row in summaries),
    "ignored": sum(row["ignored"] for row in summaries),
    "summaries": summaries,
}
(output / "test-receipt.json").write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
print(json.dumps(record, sort_keys=True))
PY

/usr/bin/chmod 0444 "$receipt_directory/input-check.log" \
    "$receipt_directory/full-tests.log" "$receipt_directory/test-receipt.json"
/usr/bin/chmod 0555 "$receipt_directory"
[[ $test_rc -eq 0 ]]
