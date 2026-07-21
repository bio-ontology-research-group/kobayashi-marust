#!/bin/bash
# Rebuild three retained historical candidate sources twice, then run each
# complete test suite. This orchestrator is intentionally sequential.

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "historical candidate rebuild failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

if [[ $(/usr/bin/hostname) != leechuck-office ]]; then
    echo "refusing build: run this only on leechuck-office (ws)" >&2
    exit 2
fi
if [[ $# -ne 1 ]]; then
    echo "usage: $0 NEW_OUTPUT_ROOT" >&2
    exit 2
fi

output_root=$(/usr/bin/readlink -m "$1")
submit_dir=$(/usr/bin/readlink -f "$(/usr/bin/dirname "$0")")
builder=$submit_dir/build_reproducible_candidate_on_ws.sh
tester=$submit_dir/test_reproducible_candidate_on_ws.sh
receipt_writer=$submit_dir/write_build_receipt.py
for path in "$builder" "$tester" "$receipt_writer"; do
    [[ -s $path && ! -L $path ]]
done
[[ ! -e $output_root ]]
if /usr/bin/pgrep -x cargo >/dev/null || /usr/bin/pgrep -x rustc >/dev/null; then
    echo "another Cargo/Rust build is running; refusing concurrent work" >&2
    exit 3
fi

labels=(a639ab5 a068059 a0d0148816c5)
commits=(
    a639ab59bfb20b04f0131a2b7b7cb727117a936b
    a0680597525b72b9d1d2c22e5d8f4b9820d8f401
    a0d0148816c560f79b8ed12a762feef5f0401056
)
compressed_sha256=(
    40a4eb56ee1efd85a56b14409a4cd95cf30308b6eec40963320351291ba92de8
    305d857b66420f43a208bee748a2c9ab545083ec626953345ac6bbf61fc88878
    34c46085d11715d5c6ad504fc3a20977917f3b453f07858f406d34ffbc8313b7
)
git_archive_sha256=(
    231ae05105ecc45dea7a5adb03bb81dd99859b8a46faf03bcf9516fad75b5a11
    bea13603606c26326cd16cf8b94ab2591531bd96a180ea660156003130c3df23
    59cebd88623b3ef1eb9c1ed325095f3e692ddf5165a475c9081af9012504162e
)

/usr/bin/mkdir -m 0755 "$output_root"
/usr/bin/mkdir -m 0755 "$output_root/sources" "$output_root/capsules" \
    "$output_root/tests"

for index in 0 1 2; do
    label=${labels[$index]}
    archive=$submit_dir/source-$label.tar.gz
    source_dir=$output_root/sources/$label
    capsule_dir=$output_root/capsules/$label
    test_dir=$output_root/tests/$label
    [[ -s $archive && ! -L $archive ]]
    [[ $(/usr/bin/sha256sum "$archive" | /usr/bin/awk '{print $1}') == "${compressed_sha256[$index]}" ]]
    [[ $(/usr/bin/gzip -dc "$archive" | /usr/bin/sha256sum | /usr/bin/awk '{print $1}') == "${git_archive_sha256[$index]}" ]]
    /usr/bin/mkdir -m 0755 "$source_dir"
    /usr/bin/tar -xzf "$archive" -C "$source_dir"
    [[ -s $source_dir/engine/Cargo.lock && -s $source_dir/engine/Cargo.toml ]]
    [[ $(/usr/bin/find "$source_dir" -type l | /usr/bin/wc -l) -eq 0 ]]
    "$builder" "$source_dir" "$capsule_dir"
    "$tester" "$capsule_dir" "$test_dir"
done

/usr/bin/python3 -I - "$output_root" "$submit_dir" \
    "${labels[*]}" "${commits[*]}" "${compressed_sha256[*]}" \
    "${git_archive_sha256[*]}" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

root = Path(sys.argv[1])
submit = Path(sys.argv[2])
labels = sys.argv[3].split()
commits = sys.argv[4].split()
compressed = sys.argv[5].split()
git_archives = sys.argv[6].split()

def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()

rows = []
for label, commit, archive_sha, git_archive_sha in zip(
    labels, commits, compressed, git_archives, strict=True
):
    capsule = root / "capsules" / label
    tests = root / "tests" / label
    build_receipt = json.loads(
        (capsule / "build-receipt.json").read_text(encoding="utf-8")
    )
    test_receipt = json.loads(
        (tests / "test-receipt.json").read_text(encoding="utf-8")
    )
    binary_sha = sha(capsule / "km-build-a")
    checks = {
        "build_verified": build_receipt.get("status")
        == "verified_reproducible",
        "builds_byte_identical": build_receipt.get("outputs", {}).get(
            "byte_identical"
        )
        is True,
        "build_a_hash": build_receipt.get("outputs", {}).get(
            "build_a_sha256"
        )
        == binary_sha,
        "build_b_hash": build_receipt.get("outputs", {}).get(
            "build_b_sha256"
        )
        == binary_sha,
        "tests_verified": test_receipt.get("status")
        == "verified_full_tests",
        "tests_pass": test_receipt.get("failed") == 0
        and test_receipt.get("return_code") == 0,
        "test_receipt_build": test_receipt.get(
            "capsule_build_receipt_sha256"
        )
        == sha(capsule / "build-receipt.json"),
    }
    if not all(checks.values()):
        raise SystemExit(
            f"receipt checks failed for {label}: "
            f"{[key for key, value in checks.items() if not value]}"
        )
    rows.append(
        {
            "label": label,
            "commit": commit,
            "retained_source_archive_sha256": archive_sha,
            "git_archive_sha256": git_archive_sha,
            "binary_sha256": binary_sha,
            "source_manifest_sha256": sha(
                capsule / "source-files.sha256"
            ),
            "build_receipt_sha256": sha(
                capsule / "build-receipt.json"
            ),
            "test_receipt_sha256": sha(tests / "test-receipt.json"),
            "passed_tests": test_receipt.get("passed"),
            "checks": checks,
        }
    )

receipt = {
    "schema_version": 1,
    "status": "verified_sequential_reproducible_builds",
    "concurrent_builds": 1,
    "build_cpus": 4,
    "orchestrator_sha256": sha(
        submit / "ws_rebuild_exact_historical_candidates.sh"
    ),
    "builder_sha256": sha(
        submit / "build_reproducible_candidate_on_ws.sh"
    ),
    "tester_sha256": sha(
        submit / "test_reproducible_candidate_on_ws.sh"
    ),
    "receipt_writer_sha256": sha(submit / "write_build_receipt.py"),
    "candidates": rows,
}
(root / "build-set-receipt.json").write_text(
    json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
print(json.dumps(receipt, sort_keys=True))
PY

(
    cd "$output_root"
    /usr/bin/find capsules tests -type f -printf '%p\0' \
        | LC_ALL=C /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$output_root/artifacts.sha256"
/usr/bin/chmod -R a-w "$output_root"
/usr/bin/cat "$output_root/build-set-receipt.json"
