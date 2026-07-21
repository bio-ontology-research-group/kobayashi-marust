#!/bin/bash
# Decisive full-IRI validation for the capsule-05 ORE 10621 candidate.
# A KM process exit is never sufficient: acceptance additionally requires the
# pinned build/source/core provenance, observed elc_cert route, and exact
# equality with a fresh same-job Konclude full-IRI fingerprint.  The retained
# fingerprint is an additional identity gate for that independently rerun oracle.
#SBATCH --job-name=km10621-fulliri-05
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
export LC_ALL=C

capsule=/ibex/scratch/hohndor/km/routing_20260715/reproducible-current-20260721-05-core
candidate_bin=$capsule/km-build-a
candidate_peer=$capsule/km-build-b
candidate_expected_sha256=7f5e39ac7e989ca7f029090d051f009a8b2f2da5d410aeccc376d9630143c0bf
source_archive=$capsule/source.tar.gz
source_archive_expected_sha256=91150f63f596e188ceae6a55f19acd0a5a9521f059cc86f0d3dc0dfee4c85f52
source_manifest=$capsule/source-files.sha256
source_manifest_expected_sha256=d5713b963d98f420939bf3843059e9edcbe06fd8c008536fee1e98202a7bf86e
source_manifest_expected_count=272
build_input_archive=$capsule/build-input.tar.gz
build_input_archive_expected_sha256=ceb06be141d847cba12dbdc987d3c4f585afbc9b2d4c2d4cb7aeea1c3546a793
build_input_manifest=$capsule/build-input-files.sha256
build_input_manifest_expected_sha256=5db9089f5663288b3b4ba1ca603e45fa7c144f2b885af1d455c7853b387aaea4
build_input_manifest_expected_count=4234
build_receipt=$capsule/build-receipt.json
build_receipt_expected_sha256=841155050f7214e88d06b64f27258a66631eeaaf4ca0f6d3949ca10bb95dca0a
build_driver=$capsule/build_reproducible_candidate_on_ws.sh
build_driver_expected_sha256=e72bd3162cb8149d3ab0acb923a938b088ee087f47f8b3e1ed2f2d2d6bb804ec
receipt_writer=$capsule/write_build_receipt.py
receipt_writer_expected_sha256=91160df6d67cf55dc39e95e9f92938c62ee24dca765ae367072f5fbc2382d462
core_expected_file_count=20
core_expected_stream_sha256=91cb83f716474e4c7c775f3eefa01f5c5fea5f3cce4cf65ef8faf659285af638

validation_driver_root=/ibex/scratch/hohndor/km/routing_20260715/validation-drivers
submit_dir=${SLURM_SUBMIT_DIR:?submit from the hash-named immutable driver directory}
validation_driver_root_canonical=$(/usr/bin/readlink -f "$validation_driver_root")
submit_dir_canonical=$(/usr/bin/readlink -f "$submit_dir")
driver_dir_name=$(/usr/bin/basename "$submit_dir_canonical")
validation_driver_expected_sha256=${driver_dir_name#sha256-}
[[ $validation_driver_expected_sha256 =~ ^[0-9a-f]{64}$ ]]
expected_driver_dir=$validation_driver_root_canonical/$driver_dir_name
/usr/bin/test "$submit_dir_canonical" = "$expected_driver_dir"
validation_driver=$submit_dir_canonical/ibex_validate_10621_fulliri_05.sbatch

validation_root=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718
oracle_root=$validation_root/results/konclude_w16_10621
oracle_fingerprint=$oracle_root/fulliri.json
oracle_fingerprint_expected_sha256=0b70bdb6a6eb2e1dbfd22337d16b163606436501dd55f78ec6be0d92dc86da55
oracle_run=$oracle_root/run.json
oracle_run_expected_sha256=bb26e5c4bace42769be54be361fd5b5ba07faaaa214ffc95c5010bfc98e893f6
oracle_taxonomy=$oracle_root/taxonomy.owl
oracle_taxonomy_expected_sha256=d50eeeef9029c705ac8219f4b7f86c21f9b6b07ef17f16c92c5128fa55a283cd
fingerprinter=$validation_root/fingerprint_tail_fulliri.py
fingerprinter_expected_sha256=b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6
konclude_bin=/ibex/scratch/hohndor/km/Konclude-official
konclude_expected_sha256=5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3
konclude_ld_library_path=/ibex/scratch/hohndor/km
konclude_pcre=$konclude_ld_library_path/libpcre.so.3
konclude_pcre_expected_sha256=18a3afc32488c647144f659d1629604df7ff58482a5734626dac65bd35eba8bd
konclude_runtime_expected_count=12
konclude_runtime_expected_stream_sha256=a65425061780e34dff5f6a460681d4599d1098906dc5b03be0ef43699406e898
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl
ontology_expected_sha256=5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167
run_root=/ibex/scratch/hohndor/km/routing_20260715/10621-fulliri-${SLURM_JOB_ID}

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

/usr/bin/test -d "$capsule"
/usr/bin/test -x "$candidate_bin"
/usr/bin/test -x "$candidate_peer"
/usr/bin/test -x "$konclude_bin"
for input in \
    "$source_archive" "$source_manifest" \
    "$build_input_archive" "$build_input_manifest" \
    "$build_receipt" "$build_driver" "$receipt_writer" \
    "$validation_driver" "$oracle_fingerprint" "$oracle_run" \
    "$oracle_taxonomy" "$fingerprinter" "$konclude_pcre" "$ontology"; do
    /usr/bin/test -s "$input"
done

/usr/bin/test "$(sha_of "$candidate_bin")" = "$candidate_expected_sha256"
/usr/bin/test "$(sha_of "$candidate_peer")" = "$candidate_expected_sha256"
/usr/bin/cmp -s "$candidate_bin" "$candidate_peer"
/usr/bin/test "$(sha_of "$source_archive")" = "$source_archive_expected_sha256"
/usr/bin/test "$(sha_of "$source_manifest")" = "$source_manifest_expected_sha256"
/usr/bin/test "$(/usr/bin/wc -l < "$source_manifest")" -eq \
    "$source_manifest_expected_count"
/usr/bin/test "$(sha_of "$build_input_archive")" = \
    "$build_input_archive_expected_sha256"
/usr/bin/test "$(sha_of "$build_input_manifest")" = \
    "$build_input_manifest_expected_sha256"
/usr/bin/test "$(/usr/bin/wc -l < "$build_input_manifest")" -eq \
    "$build_input_manifest_expected_count"
/usr/bin/test "$(sha_of "$build_receipt")" = "$build_receipt_expected_sha256"
/usr/bin/test "$(sha_of "$build_driver")" = "$build_driver_expected_sha256"
/usr/bin/test "$(sha_of "$receipt_writer")" = "$receipt_writer_expected_sha256"
/usr/bin/test "$(sha_of "$validation_driver")" = \
    "$validation_driver_expected_sha256"
/usr/bin/test "$(sha_of "$oracle_fingerprint")" = \
    "$oracle_fingerprint_expected_sha256"
/usr/bin/test "$(sha_of "$oracle_run")" = "$oracle_run_expected_sha256"
/usr/bin/test "$(sha_of "$oracle_taxonomy")" = \
    "$oracle_taxonomy_expected_sha256"
/usr/bin/test "$(sha_of "$fingerprinter")" = "$fingerprinter_expected_sha256"
/usr/bin/test "$(sha_of "$konclude_bin")" = "$konclude_expected_sha256"
/usr/bin/test "$(sha_of "$konclude_pcre")" = \
    "$konclude_pcre_expected_sha256"
/usr/bin/test "$(sha_of "$ontology")" = "$ontology_expected_sha256"

/usr/bin/mkdir -p "$run_root"
cpu_model=$(/usr/bin/awk -F: \
    '/^model name[[:space:]]*:/ {sub(/^[[:space:]]+/, "", $2); print $2; exit}' \
    /proc/cpuinfo)
[[ -n $cpu_model ]]
konclude_runtime_manifest=$run_root/konclude-runtime-libraries.sha256
konclude_runtime_paths=$(
    /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
        LD_LIBRARY_PATH="$konclude_ld_library_path" \
        /usr/bin/ldd "$konclude_bin" \
        | /usr/bin/awk \
            '$2 == "=>" && $3 ~ /^\// {print $3} $1 ~ /^\// {print $1}' \
        | /usr/bin/sort -u
)
/usr/bin/printf '%s\n' "$konclude_runtime_paths" \
    | /usr/bin/xargs /usr/bin/sha256sum \
    > "$konclude_runtime_manifest"
konclude_runtime_count=$(/usr/bin/wc -l < "$konclude_runtime_manifest")
konclude_runtime_stream_sha256=$(sha_of "$konclude_runtime_manifest")
/usr/bin/test "$konclude_runtime_count" -eq \
    "$konclude_runtime_expected_count"
/usr/bin/test "$konclude_runtime_stream_sha256" = \
    "$konclude_runtime_expected_stream_sha256"
core_file_count=$(
    /usr/bin/find "$capsule" -maxdepth 1 -type f -printf '.' | /usr/bin/wc -c
)
(
    cd "$capsule"
    /usr/bin/find . -maxdepth 1 -type f -printf '%f\0' \
        | /usr/bin/sort -z \
        | /usr/bin/xargs -0 /usr/bin/sha256sum \
        > "$run_root/core-files.sha256"
)
core_stream_sha256=$(sha_of "$run_root/core-files.sha256")
/usr/bin/test "$core_file_count" -eq "$core_expected_file_count"
/usr/bin/test "$core_stream_sha256" = "$core_expected_stream_sha256"

/usr/bin/sha256sum \
    "$candidate_bin" "$candidate_peer" \
    "$source_archive" "$source_manifest" \
    "$build_input_archive" "$build_input_manifest" \
    "$build_receipt" "$build_driver" "$receipt_writer" \
    "$validation_driver" "$ontology" "$fingerprinter" "$konclude_bin" \
    "$konclude_pcre" "$konclude_runtime_manifest" \
    "$oracle_fingerprint" "$oracle_run" "$oracle_taxonomy" \
    > "$run_root/inputs.sha256"

/usr/bin/python3 - \
    "$run_root/core-check.json" "$core_file_count" "$core_stream_sha256" \
    "$core_expected_file_count" "$core_expected_stream_sha256" <<'PY'
import json
from pathlib import Path
import sys

actual_count, expected_count = int(sys.argv[2]), int(sys.argv[4])
actual_stream, expected_stream = sys.argv[3], sys.argv[5]
checks = {
    "file_count": actual_count == expected_count,
    "sorted_file_hash_stream": actual_stream == expected_stream,
}
record = {
    "schema_version": 1,
    "status": "ok" if all(checks.values()) else "mismatch",
    "checks": checks,
    "actual_file_count": actual_count,
    "expected_file_count": expected_count,
    "actual_stream_sha256": actual_stream,
    "expected_stream_sha256": expected_stream,
}
Path(sys.argv[1]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
if record["status"] != "ok":
    raise SystemExit(1)
PY

/usr/bin/python3 - \
    "$run_root/konclude-runtime-check.json" \
    "$konclude_runtime_count" "$konclude_runtime_stream_sha256" \
    "$konclude_runtime_expected_count" \
    "$konclude_runtime_expected_stream_sha256" \
    "$(sha_of "$konclude_pcre")" "$konclude_pcre_expected_sha256" <<'PY'
import json
from pathlib import Path
import sys

actual_count, expected_count = int(sys.argv[2]), int(sys.argv[4])
actual_stream, expected_stream = sys.argv[3], sys.argv[5]
actual_pcre, expected_pcre = sys.argv[6], sys.argv[7]
checks = {
    "library_count": actual_count == expected_count,
    "sorted_resolved_library_hash_stream": actual_stream == expected_stream,
    "pinned_pcre": actual_pcre == expected_pcre,
}
record = {
    "schema_version": 1,
    "status": "ok" if all(checks.values()) else "mismatch",
    "checks": checks,
    "actual_library_count": actual_count,
    "expected_library_count": expected_count,
    "actual_stream_sha256": actual_stream,
    "expected_stream_sha256": expected_stream,
    "actual_pcre_sha256": actual_pcre,
    "expected_pcre_sha256": expected_pcre,
}
Path(sys.argv[1]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
if record["status"] != "ok":
    raise SystemExit(1)
PY

# A receipt hash identifies a document; these checks establish that the
# document actually binds every build input and resolved tool used here.
/usr/bin/python3 - \
    "$build_receipt" "$run_root/build-receipt-check.json" <<'PY'
import json
from pathlib import Path
import re
import sys

receipt = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
output_path = Path(sys.argv[2])
build = receipt.get("build", {})
build_input = receipt.get("build_input", {})
container = receipt.get("container", {})
outputs = receipt.get("outputs", {})
source = receipt.get("source", {})
toolchain = receipt.get("toolchain", {})
expected_binary = "7f5e39ac7e989ca7f029090d051f009a8b2f2da5d410aeccc376d9630143c0bf"
expected_command = [
    "cargo", "build", "--release", "--locked", "--offline", "-j4", "--bin", "km"
]
checks = {
    "status_verified_reproducible": receipt.get("status") == "verified_reproducible",
    "byte_identical": outputs.get("byte_identical") is True,
    "binary_hash": outputs.get("binary_sha256") == expected_binary,
    "build_a_hash": outputs.get("build_a_sha256") == expected_binary,
    "build_b_hash": outputs.get("build_b_sha256") == expected_binary,
    "source_archive": source.get("archive_sha256")
    == "91150f63f596e188ceae6a55f19acd0a5a9521f059cc86f0d3dc0dfee4c85f52",
    "source_manifest": source.get("manifest_sha256")
    == "d5713b963d98f420939bf3843059e9edcbe06fd8c008536fee1e98202a7bf86e",
    "source_manifest_count": source.get("manifest_file_count") == 272,
    "source_cargo_lock": source.get("cargo_lock_sha256")
    == "f984323988b157fe566fb3d9a92c14b152820ad60631f3a9c1c3d5db9abc890b",
    "build_input_archive": build_input.get("archive_sha256")
    == "ceb06be141d847cba12dbdc987d3c4f585afbc9b2d4c2d4cb7aeea1c3546a793",
    "build_input_manifest": build_input.get("manifest_sha256")
    == "5db9089f5663288b3b4ba1ca603e45fa7c144f2b885af1d455c7853b387aaea4",
    "build_input_count": build_input.get("manifest_file_count") == 4234,
    "vendored_input": build_input.get("includes_vendored_dependencies") is True,
    "build_command": build.get("command") == expected_command,
    "build_limits": build.get("cpus") == 4
    and build.get("jobs") == 4
    and build.get("memory_gib") == 16,
    "cargo_locked": build.get("cargo_locked") is True,
    "offline_vendored": build.get("offline_vendored") is True,
    "network_disabled": build.get("network_disabled") is True,
    "source_date_epoch": build.get("source_date_epoch") == 0,
    "build_driver": build.get("driver_sha256")
    == "e72bd3162cb8149d3ab0acb923a938b088ee087f47f8b3e1ed2f2d2d6bb804ec",
    "receipt_writer": build.get("receipt_writer_sha256")
    == "91160df6d67cf55dc39e95e9f92938c62ee24dca765ae367072f5fbc2382d462",
    "container_digest": container.get("image_digest")
    == "sha256:646e8ceea789b00c5cfa339816a3ed44940dbf1651dc167b78f3c0aefcae0025",
    "container_image_id": container.get("image_id")
    == "sha256:fe20d8a383d5ea8c1bf65f21c14e9bbb5a64b1ef4507f8efdb57e53fb2a080f0",
    "container_image_ref": container.get("image_ref")
    == "rust@sha256:646e8ceea789b00c5cfa339816a3ed44940dbf1651dc167b78f3c0aefcae0025",
    "rustc_path": toolchain.get("rustc_path")
    == "/usr/local/rustup/toolchains/1.95.0-x86_64-unknown-linux-gnu/bin/rustc",
    "rustc_hash": toolchain.get("rustc_sha256")
    == "bff349e72704ff70bc08a234a3847338e797065bbedde5e556808bc87b7bf7c6",
    "rustc_commit": bool(re.search(
        r"(?m)^commit-hash:\s*59807616e1fa2540724bfbac14d7976d7e4a3860$",
        toolchain.get("rustc_version_verbose", ""),
    )),
    "cargo_path": toolchain.get("cargo_path")
    == "/usr/local/rustup/toolchains/1.95.0-x86_64-unknown-linux-gnu/bin/cargo",
    "cargo_hash": toolchain.get("cargo_sha256")
    == "841072d1d92f9e841d9ba5b0814182a0adf064acf4527cd120967b7bc49dcb66",
    "rustup_path": toolchain.get("rustup_path") == "/usr/local/cargo/bin/rustup",
    "rustup_hash": toolchain.get("rustup_sha256")
    == "4acc9acc76d5079515b46346a485974457b5a79893cfb01112423c89aeb5aa10",
}
record = {
    "schema_version": 2,
    "status": "ok" if all(checks.values()) else "mismatch",
    "checks": checks,
}
tmp = Path(str(output_path) + ".tmp")
tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
tmp.replace(output_path)
if record["status"] != "ok":
    raise SystemExit(1)
PY

# Bind the retained fingerprint to its original Konclude run, exact ontology,
# and primary OWL/XML taxonomy before treating it as the oracle.
/usr/bin/python3 - \
    "$oracle_fingerprint" "$oracle_run" "$oracle_taxonomy_expected_sha256" \
    "$ontology_expected_sha256" "$run_root/oracle-check.json" <<'PY'
import json
from pathlib import Path
import sys

fingerprint = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
run = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
taxonomy_sha, ontology_sha = sys.argv[3:5]
checks = {
    "fingerprint_status": fingerprint.get("status") == "ok",
    "fingerprint_algorithm": fingerprint.get("algorithm")
    == "full-iri-scc-component-bitset-fingerprint-v1",
    "fingerprint_input": fingerprint.get("input_sha256") == taxonomy_sha,
    "fingerprint_ontology": fingerprint.get("source_ontology_sha256") == ontology_sha,
    "known_taxonomy": fingerprint.get("taxonomy_sha256")
    == "066b41b5f3e845110eceb3607b050627da744968ccef1ceafed50e3c3ea4468e",
    "run_status": run.get("status") == "ok" and run.get("return_code") == 0,
    "run_output": run.get("primary_output_sha256") == taxonomy_sha,
    "run_ontology": run.get("ontology_sha256") == ontology_sha,
    "run_limits": run.get("timeout_s") == 240.0
    and run.get("memory_limit_mb") == 20480
    and run.get("cpus") == 16,
    "run_konclude": run.get("binary_sha256")
    == "5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3",
}
record = {
    "schema_version": 1,
    "status": "ok" if all(checks.values()) else "mismatch",
    "checks": checks,
}
Path(sys.argv[5]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
if record["status"] != "ok":
    raise SystemExit(1)
PY

# Reproduce the independent oracle inside this same allocation.  The command,
# binary, ontology, timeout, memory request and CPU count match the retained
# reference run exactly.
fresh_taxonomy=$run_root/fresh.owl
fresh_started=$(/usr/bin/date --iso-8601=seconds)
set +e
/usr/bin/time -v -o "$run_root/fresh-konclude.time" \
    /usr/bin/timeout -k 10 240 \
    /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
        LD_LIBRARY_PATH="$konclude_ld_library_path" \
        "$konclude_bin" classification -w 16 -v \
        -i "$ontology" -o "$fresh_taxonomy" \
    > "$run_root/fresh-konclude.stdout" \
    2> "$run_root/fresh-konclude.stderr"
fresh_rc=$?
set -e
fresh_finished=$(/usr/bin/date --iso-8601=seconds)
fresh_peak_kib=$(/usr/bin/awk -F: \
    '/Maximum resident set size/ {gsub(/[[:space:]]/, "", $2); print $2}' \
    "$run_root/fresh-konclude.time")
[[ $fresh_peak_kib =~ ^[0-9]+$ ]]
if /usr/bin/test -s "$fresh_taxonomy"; then
    fresh_taxonomy_sha256=$(sha_of "$fresh_taxonomy")
    fresh_taxonomy_bytes=$(/usr/bin/stat -c %s "$fresh_taxonomy")
else
    fresh_taxonomy_sha256=missing
    fresh_taxonomy_bytes=0
fi

/usr/bin/python3 - \
    "$run_root/fresh-konclude-run.json" "$fresh_rc" \
    "$fresh_started" "$fresh_finished" "$fresh_peak_kib" \
    "$fresh_taxonomy" "$fresh_taxonomy_sha256" "$fresh_taxonomy_bytes" \
    "$cpu_model" "$konclude_runtime_manifest" \
    "$konclude_runtime_stream_sha256" "$konclude_runtime_count" \
    "$konclude_pcre" "$konclude_pcre_expected_sha256" \
    "$konclude_ld_library_path" <<'PY'
import json
from pathlib import Path
import sys

rc = int(sys.argv[2])
output_path = Path(sys.argv[6])
record = {
    "schema_version": 1,
    "kind": "fresh-konclude-oracle",
    "status": "ok" if rc == 0 and output_path.is_file() and output_path.stat().st_size else "failed",
    "return_code": rc,
    "command": [
        "/ibex/scratch/hohndor/km/Konclude-official",
        "classification", "-w", "16", "-v", "-i",
        "/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl",
        "-o", str(output_path),
    ],
    "binary_sha256": "5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3",
    "ontology_sha256": "5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167",
    "started": sys.argv[3],
    "finished": sys.argv[4],
    "maximum_resident_kib": int(sys.argv[5]),
    "primary_output": str(output_path),
    "primary_output_sha256": sys.argv[7],
    "primary_output_bytes": int(sys.argv[8]),
    "timeout_seconds": 240,
    "slurm_cpus": 16,
    "slurm_memory": "20G",
    "cpu_model": sys.argv[9],
    "environment": {
        "LC_ALL": "C",
        "LD_LIBRARY_PATH": sys.argv[15],
        "PATH": "/usr/bin:/bin",
    },
    "runtime_libraries": {
        "manifest": sys.argv[10],
        "manifest_sha256": sys.argv[11],
        "count": int(sys.argv[12]),
        "required_pcre": sys.argv[13],
        "required_pcre_sha256": sys.argv[14],
    },
}
Path(sys.argv[1]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
if record["status"] != "ok":
    raise SystemExit(1)
PY
/usr/bin/test "$fresh_rc" -eq 0
/usr/bin/test -s "$fresh_taxonomy"

/usr/bin/time -v -o "$run_root/fresh-konclude-fingerprint.time" \
    /usr/bin/python3 "$fingerprinter" \
    --input "$fresh_taxonomy" \
    --format owlxml \
    --source-ontology "$ontology" \
    --output-prefix "$run_root/fresh-konclude-fulliri" \
    > "$run_root/fresh-konclude-fingerprint.stdout" \
    2> "$run_root/fresh-konclude-fingerprint.stderr"

# Require both the known taxonomy/counts and field-for-field identity with the
# retained, source-bound Konclude fingerprint.
/usr/bin/python3 - \
    "$run_root/fresh-konclude-fulliri.json" "$oracle_fingerprint" \
    "$fresh_taxonomy_sha256" "$run_root/fresh-konclude-run.json" \
    "$run_root/fresh-oracle-check.json" <<'PY'
import json
from pathlib import Path
import sys

fresh = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
retained = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
fresh_output_sha = sys.argv[3]
run = json.loads(Path(sys.argv[4]).read_text(encoding="utf-8"))
fields = [
    "algorithm",
    "status",
    "consistent",
    "taxonomy_sha256",
    "subsumptions",
    "unsatisfiable",
    "nonempty_lefts",
    "components",
    "ontology_declarations",
    "source_ontology_sha256",
]
differences = {
    field: {"fresh": fresh.get(field), "retained": retained.get(field)}
    for field in fields
    if fresh.get(field) != retained.get(field)
}
checks = {
    "input_hash": fresh.get("input_sha256") == fresh_output_sha,
    "algorithm": fresh.get("algorithm")
    == "full-iri-scc-component-bitset-fingerprint-v1",
    "status": fresh.get("status") == "ok",
    "consistent": fresh.get("consistent") is True,
    "known_taxonomy": fresh.get("taxonomy_sha256")
    == "066b41b5f3e845110eceb3607b050627da744968ccef1ceafed50e3c3ea4468e",
    "known_subsumptions": fresh.get("subsumptions") == 70827,
    "known_unsatisfiable": fresh.get("unsatisfiable") == 33433,
    "known_nonempty_lefts": fresh.get("nonempty_lefts") == 8209,
    "known_components": fresh.get("components") == 8215,
    "known_declarations": fresh.get("ontology_declarations") == 41647,
    "ontology": fresh.get("source_ontology_sha256")
    == "5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167",
    "run_status": run.get("status") == "ok" and run.get("return_code") == 0,
    "run_command": run.get("command", [])[:8] == [
        "/ibex/scratch/hohndor/km/Konclude-official",
        "classification", "-w", "16", "-v", "-i",
        "/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl", "-o",
    ] and run.get("command", [])[-1].endswith("/fresh.owl"),
    "run_binary": run.get("binary_sha256")
    == "5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3",
    "run_ontology": run.get("ontology_sha256")
    == "5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167",
    "run_output": run.get("primary_output_sha256") == fresh_output_sha,
    "run_limits": run.get("timeout_seconds") == 240
    and run.get("slurm_cpus") == 16
    and run.get("slurm_memory") == "20G",
    "run_environment": run.get("environment") == {
        "LC_ALL": "C",
        "LD_LIBRARY_PATH": "/ibex/scratch/hohndor/km",
        "PATH": "/usr/bin:/bin",
    },
    "run_runtime_libraries": run.get("runtime_libraries", {}).get("count") == 12
    and run.get("runtime_libraries", {}).get("manifest_sha256")
    == "a65425061780e34dff5f6a460681d4599d1098906dc5b03be0ef43699406e898"
    and run.get("runtime_libraries", {}).get("required_pcre")
    == "/ibex/scratch/hohndor/km/libpcre.so.3"
    and run.get("runtime_libraries", {}).get("required_pcre_sha256")
    == "18a3afc32488c647144f659d1629604df7ff58482a5734626dac65bd35eba8bd",
    "retained_identity": not differences,
}
record = {
    "schema_version": 1,
    "status": "ok" if all(checks.values()) else "mismatch",
    "checks": checks,
    "checked_fields": fields,
    "differences": differences,
}
Path(sys.argv[5]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
if record["status"] != "ok":
    raise SystemExit(1)
PY
fresh_fingerprint_sha256=$(sha_of "$run_root/fresh-konclude-fulliri.json")

# env -i prevents inherited KM switches. Diagnostic lower and debug tracing
# are absent; only the named route's bounded search controls and timing remain.
started=$(/usr/bin/date --iso-8601=seconds)
set +e
/usr/bin/time -v -o "$run_root/km.time" \
    /usr/bin/timeout -k 10 240 \
    /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
        KM_TIMING=1 \
        KM_ELC_COVER_MODELS=2 \
        KM_ELC_TARGET_MODELS=32 \
        KM_ELC_TARGET_RESTARTS=64 \
        "$candidate_bin" classify --route elc_cert "$ontology" \
    > "$run_root/km.json" 2> "$run_root/km.stderr"
km_rc=$?
set -e
finished=$(/usr/bin/date --iso-8601=seconds)
km_peak_kib=$(/usr/bin/awk -F: \
    '/Maximum resident set size/ {gsub(/[[:space:]]/, "", $2); print $2}' \
    "$run_root/km.time")
[[ $km_peak_kib =~ ^[0-9]+$ ]]

{
    echo "job_id=$SLURM_JOB_ID"
    echo "host=$(/usr/bin/hostname)"
    echo "cpu_model=$cpu_model"
    echo "acceptance_evidence=pending_fulliri_match"
    echo "fresh_konclude_started=$fresh_started"
    echo "fresh_konclude_finished=$fresh_finished"
    echo "fresh_konclude_return_code=$fresh_rc"
    echo "fresh_konclude_command=/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C LD_LIBRARY_PATH=$konclude_ld_library_path $konclude_bin classification -w 16 -v -i $ontology -o $fresh_taxonomy"
    echo "fresh_konclude_maximum_resident_kib=$fresh_peak_kib"
    echo "fresh_konclude_output_sha256=$fresh_taxonomy_sha256"
    echo "fresh_konclude_fingerprint_sha256=$fresh_fingerprint_sha256"
    echo "fresh_konclude_runtime_library_count=$konclude_runtime_count"
    echo "fresh_konclude_runtime_stream_sha256=$konclude_runtime_stream_sha256"
    echo "fresh_konclude_pcre_sha256=$konclude_pcre_expected_sha256"
    echo "started=$started"
    echo "finished=$finished"
    echo "km_return_code=$km_rc"
    echo "command=/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C KM_TIMING=1 KM_ELC_COVER_MODELS=2 KM_ELC_TARGET_MODELS=32 KM_ELC_TARGET_RESTARTS=64 $candidate_bin classify --route elc_cert $ontology"
    echo "route=elc_cert"
    echo "route_bundle=KM_THREADS=16,KM_PAR_MEM_GB=18,KM_HT_MEM_GB=18,KM_KEEP_CHAIN_AXIOMS=1,KM_MECHANISM=elc,KM_NO_HT_RULES=1,KM_NO_HT_RACE=1,KM_NO_ABSORB_PORTFOLIO=1,KM_ABSORB=0,KM_ELC_FORCE=1,KM_ELC_CERT=2"
    echo "search_controls=KM_ELC_COVER_MODELS=2,KM_ELC_TARGET_MODELS=32,KM_ELC_TARGET_RESTARTS=64"
    echo "instrumentation=KM_TIMING=1"
    echo "diagnostic_lower=absent_from_env_i"
    echo "debug=absent_from_env_i"
    echo "certificate_soundness=search-only choices; admitted states reclose EL, satisfy all residuals, keep TOP nonbottom, and witness an empty extra-label intersection for every base-alive named subject"
    echo "slurm_cpus=$SLURM_CPUS_PER_TASK"
    echo "slurm_memory=20G"
    echo "timeout_seconds=240"
    echo "maximum_resident_kib=$km_peak_kib"
    echo "validation_driver_sha256=$validation_driver_expected_sha256"
    echo "capsule_core_stream_sha256=$core_stream_sha256"
    echo "km_sha256=$candidate_expected_sha256"
    echo "source_archive_sha256=$source_archive_expected_sha256"
    echo "source_manifest_sha256=$source_manifest_expected_sha256"
    echo "build_input_archive_sha256=$build_input_archive_expected_sha256"
    echo "build_input_manifest_sha256=$build_input_manifest_expected_sha256"
    echo "build_receipt_sha256=$build_receipt_expected_sha256"
    echo "ontology_sha256=$ontology_expected_sha256"
    echo "fingerprinter_sha256=$fingerprinter_expected_sha256"
    echo "konclude_sha256=$konclude_expected_sha256"
    echo "oracle_fingerprint_sha256=$oracle_fingerprint_expected_sha256"
    echo "oracle_run_sha256=$oracle_run_expected_sha256"
    echo "oracle_taxonomy_sha256=$oracle_taxonomy_expected_sha256"
} > "$run_root/run.meta"

/usr/bin/test "$km_rc" -eq 0
/usr/bin/test -s "$run_root/km.json"
/usr/bin/grep -q 'KM_TIMING frontend done.* route=elc_cert' "$run_root/km.stderr"
/usr/bin/python3 - "$run_root/km.stderr" "$run_root/route-check.json" <<'PY'
import json
from pathlib import Path
import re
import sys

lines = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace").splitlines()
matches = [line for line in lines if re.search(r"KM_TIMING frontend done.* route=elc_cert", line)]
checks = {
    "exact_route_trace": len(matches) == 1,
    "no_diagnostic_lower_marker": not any("DIAGNOSTIC_LOWER" in line for line in lines),
}
record = {
    "schema_version": 1,
    "status": "ok" if all(checks.values()) else "mismatch",
    "checks": checks,
    "route_trace": matches,
}
Path(sys.argv[2]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
if record["status"] != "ok":
    raise SystemExit(1)
PY

/usr/bin/time -v -o "$run_root/fingerprint.time" \
    /usr/bin/python3 "$fingerprinter" \
    --input "$run_root/km.json" \
    --format json \
    --source-ontology "$ontology" \
    --output-prefix "$run_root/km-fulliri" \
    > "$run_root/fingerprint.stdout" 2> "$run_root/fingerprint.stderr"

/usr/bin/python3 - \
    "$run_root/km-fulliri.json" "$run_root/fresh-konclude-fulliri.json" \
    "$run_root/comparison.json" <<'PY'
import json
from pathlib import Path
import sys

candidate = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
oracle = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
output_path = Path(sys.argv[3])
fields = [
    "algorithm",
    "status",
    "consistent",
    "taxonomy_sha256",
    "subsumptions",
    "unsatisfiable",
    "nonempty_lefts",
    "components",
    "ontology_declarations",
    "source_ontology_sha256",
]
differences = {
    field: {"candidate": candidate.get(field), "konclude": oracle.get(field)}
    for field in fields
    if candidate.get(field) != oracle.get(field)
}
record = {
    "schema_version": 1,
    "ontology": 10621,
    "route": "elc_cert",
    "oracle": "fresh same-job Konclude",
    "status": "match" if not differences else "mismatch",
    "checked_fields": fields,
    "differences": differences,
    "candidate": {field: candidate.get(field) for field in fields},
    "konclude": {field: oracle.get(field) for field in fields},
}
tmp = Path(str(output_path) + ".tmp")
tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
tmp.replace(output_path)
if differences:
    raise SystemExit(1)
PY

# Only this final conjunction creates acceptance evidence.
/usr/bin/python3 - \
    "$run_root/build-receipt-check.json" "$run_root/core-check.json" \
    "$run_root/konclude-runtime-check.json" "$run_root/oracle-check.json" \
    "$run_root/fresh-oracle-check.json" "$run_root/route-check.json" \
    "$run_root/comparison.json" \
    "$run_root/acceptance-evidence.json" <<'PY'
import json
from pathlib import Path
import sys

receipt, core, runtime, retained_oracle, fresh_oracle, route, comparison = [
    json.loads(Path(path).read_text(encoding="utf-8")) for path in sys.argv[1:8]
]
checks = {
    "build_receipt": receipt.get("status") == "ok",
    "capsule_core": core.get("status") == "ok",
    "konclude_runtime": runtime.get("status") == "ok",
    "retained_oracle": retained_oracle.get("status") == "ok",
    "fresh_same_job_oracle": fresh_oracle.get("status") == "ok",
    "route_trace": route.get("status") == "ok",
    "fulliri_exact_match": comparison.get("status") == "match"
    and comparison.get("differences") == {},
}
record = {
    "schema_version": 1,
    "ontology": 10621,
    "route": "elc_cert",
    "status": "accepted" if all(checks.values()) else "rejected",
    "acceptance_evidence": all(checks.values()),
    "checks": checks,
}
tmp = Path(sys.argv[8] + ".tmp")
tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
tmp.replace(Path(sys.argv[8]))
if not record["acceptance_evidence"]:
    raise SystemExit(1)
PY

# Promote the human-readable run record only after the exact final conjunction
# above has created affirmative machine-readable acceptance evidence.
/usr/bin/sed -i \
    's/^acceptance_evidence=pending_fulliri_match$/acceptance_evidence=true/' \
    "$run_root/run.meta"
/usr/bin/grep -qx 'acceptance_evidence=true' "$run_root/run.meta"

/usr/bin/sha256sum \
    "$run_root/inputs.sha256" \
    "$run_root/konclude-runtime-libraries.sha256" \
    "$run_root/konclude-runtime-check.json" \
    "$run_root/fresh.owl" "$run_root/fresh-konclude-run.json" \
    "$run_root/fresh-konclude.stdout" "$run_root/fresh-konclude.stderr" \
    "$run_root/fresh-konclude.time" \
    "$run_root/fresh-konclude-fingerprint.stdout" \
    "$run_root/fresh-konclude-fingerprint.stderr" \
    "$run_root/fresh-konclude-fingerprint.time" \
    "$run_root/fresh-konclude-fulliri.json" \
    "$run_root/fresh-konclude-fulliri.nodes.tsv.gz" \
    "$run_root/fresh-konclude-fulliri.unsat.txt.gz" \
    "$run_root/fresh-oracle-check.json" \
    "$run_root/km.json" "$run_root/km.stderr" "$run_root/km.time" \
    "$run_root/fingerprint.stdout" "$run_root/fingerprint.stderr" \
    "$run_root/fingerprint.time" \
    "$run_root/km-fulliri.json" "$run_root/km-fulliri.nodes.tsv.gz" \
    "$run_root/km-fulliri.unsat.txt.gz" "$run_root/comparison.json" \
    "$run_root/build-receipt-check.json" "$run_root/core-check.json" \
    "$run_root/oracle-check.json" "$run_root/route-check.json" \
    "$run_root/acceptance-evidence.json" "$run_root/core-files.sha256" \
    "$run_root/run.meta" \
    > "$run_root/outputs.sha256"
/usr/bin/cat "$run_root/acceptance-evidence.json"
/usr/bin/cat "$run_root/comparison.json"
