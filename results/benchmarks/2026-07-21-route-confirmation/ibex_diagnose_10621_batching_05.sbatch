#!/bin/bash
# NON-ACCEPTANCE DIAGNOSTIC for the capsule-05 ORE 10621 candidate.
#
# This runs the exact frontend plus ELC worker trace needed to measure the new
# local-dead protected-target batching tier. It never fingerprints or accepts a
# taxonomy. Every result is unconditionally marked acceptance_evidence=false.
#SBATCH --job-name=km10621-batch05-diag
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

diagnostic_driver_root=/ibex/scratch/hohndor/km/routing_20260715/diagnostic-drivers
submit_dir=${SLURM_SUBMIT_DIR:?submit from the hash-named immutable driver directory}
diagnostic_driver_root_canonical=$(/usr/bin/readlink -f "$diagnostic_driver_root")
submit_dir_canonical=$(/usr/bin/readlink -f "$submit_dir")
driver_dir_name=$(/usr/bin/basename "$submit_dir_canonical")
diagnostic_driver_expected_sha256=${driver_dir_name#sha256-}
[[ $diagnostic_driver_expected_sha256 =~ ^[0-9a-f]{64}$ ]]
expected_driver_dir=$diagnostic_driver_root_canonical/$driver_dir_name
/usr/bin/test "$submit_dir_canonical" = "$expected_driver_dir"
diagnostic_driver=$submit_dir_canonical/ibex_diagnose_10621_batching_05.sbatch

ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl
ontology_expected_sha256=5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167
run_root=/ibex/scratch/hohndor/km/routing_20260715/10621-batching-05-${SLURM_JOB_ID}

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

/usr/bin/test -d "$capsule"
/usr/bin/test -x "$candidate_bin"
/usr/bin/test -x "$candidate_peer"
for input in \
    "$source_archive" "$source_manifest" \
    "$build_input_archive" "$build_input_manifest" \
    "$build_receipt" "$build_driver" "$receipt_writer" \
    "$diagnostic_driver" "$ontology"; do
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
/usr/bin/test "$(sha_of "$diagnostic_driver")" = \
    "$diagnostic_driver_expected_sha256"
/usr/bin/test "$(sha_of "$ontology")" = "$ontology_expected_sha256"

/usr/bin/mkdir -p "$run_root"
cpu_model=$(/usr/bin/awk -F: \
    '/^model name[[:space:]]*:/ {sub(/^[[:space:]]+/, "", $2); print $2; exit}' \
    /proc/cpuinfo)
[[ -n $cpu_model ]]
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
    "$diagnostic_driver" "$ontology" "$run_root/core-files.sha256" \
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

# The diagnostic still requires the exact receipt and complete build identity.
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

clauses=$run_root/clauses.json
meta=$run_root/meta.json
frontend_started=$(/usr/bin/date --iso-8601=seconds)
set +e
/usr/bin/time -v -o "$run_root/ofn.time" \
    /usr/bin/timeout -k 10 240 \
    /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C KM_ROUTE=elc_cert \
        "$candidate_bin" ofn "$ontology" --meta "$meta" \
    > "$clauses" 2> "$run_root/ofn.stderr"
ofn_rc=$?
set -e
frontend_finished=$(/usr/bin/date --iso-8601=seconds)
/usr/bin/test "$ofn_rc" -eq 0
/usr/bin/test -s "$clauses"
/usr/bin/test -s "$meta"
/usr/bin/sha256sum "$clauses" "$meta" > "$run_root/frontend.sha256"
clauses_sha256=$(sha_of "$clauses")
meta_sha256=$(sha_of "$meta")

/usr/bin/python3 - "$meta" "$run_root/frontend-check.json" <<'PY'
import json
from pathlib import Path
import sys

meta = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
checks = {"route": meta.get("route") == "elc_cert"}
record = {
    "schema_version": 1,
    "status": "ok" if all(checks.values()) else "mismatch",
    "checks": checks,
    "route": meta.get("route"),
    "el_rbox_safe": meta.get("el_rbox_safe"),
}
Path(sys.argv[2]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
if record["status"] != "ok":
    raise SystemExit(1)
PY

/usr/bin/python3 - \
    "$run_root/invocations.json" "$candidate_bin" "$candidate_expected_sha256" \
    "$ontology" "$ontology_expected_sha256" "$clauses" "$clauses_sha256" \
    "$meta" "$meta_sha256" "$diagnostic_driver_expected_sha256" <<'PY'
import json
from pathlib import Path
import sys

candidate, ontology, clauses, meta = sys.argv[2], sys.argv[4], sys.argv[6], sys.argv[8]
record = {
    "schema_version": 1,
    "purpose": "non-acceptance capsule-05 protected-target batching diagnostic",
    "acceptance_evidence": False,
    "diagnostic_driver_sha256": sys.argv[10],
    "binary_sha256": sys.argv[3],
    "ontology_sha256": sys.argv[5],
    "frontend": {
        "command": [
            "/usr/bin/timeout", "-k", "10", "240", "/usr/bin/env", "-i",
            "PATH=/usr/bin:/bin", "LC_ALL=C", "KM_ROUTE=elc_cert",
            candidate, "ofn", ontology, "--meta", meta,
        ],
        "environment": {
            "LC_ALL": "C",
            "KM_ROUTE": "elc_cert",
            "PATH": "/usr/bin:/bin",
        },
        "stdout": clauses,
        "stdout_sha256": sys.argv[7],
        "meta": meta,
        "meta_sha256": sys.argv[9],
    },
    "worker": {
        "command": [
            "/usr/bin/timeout", "-k", "10", "240", "/usr/bin/env", "-i",
            "PATH=/usr/bin:/bin", "LC_ALL=C", "KM_ELC_CERT=2",
            "KM_ELC_COVER_MODELS=2", "KM_ELC_TARGET_MODELS=32",
            "KM_ELC_TARGET_RESTARTS=64", "KM_ELC_DEBUG=1",
            "KM_ELC_DEBUG_ITEMS=0", "KM_ELC_TIMING=1", candidate, "elc",
        ],
        "environment": {
            "LC_ALL": "C",
            "KM_ELC_CERT": "2",
            "KM_ELC_COVER_MODELS": "2",
            "KM_ELC_DEBUG": "1",
            "KM_ELC_DEBUG_ITEMS": "0",
            "KM_ELC_TARGET_MODELS": "32",
            "KM_ELC_TARGET_RESTARTS": "64",
            "KM_ELC_TIMING": "1",
            "PATH": "/usr/bin:/bin",
        },
        "stdin": clauses,
        "stdin_sha256": sys.argv[7],
    },
    "explicitly_absent": ["KM_ELC_DIAGNOSTIC_LOWER"],
    "limits": {"timeout_seconds": 240, "slurm_cpus": 16, "slurm_memory": "20G"},
}
Path(sys.argv[1]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
PY

worker_started=$(/usr/bin/date --iso-8601=seconds)
set +e
/usr/bin/time -v -o "$run_root/elc.time" \
    /usr/bin/timeout -k 10 240 \
    /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
        KM_ELC_CERT=2 \
        KM_ELC_COVER_MODELS=2 \
        KM_ELC_TARGET_MODELS=32 \
        KM_ELC_TARGET_RESTARTS=64 \
        KM_ELC_DEBUG=1 \
        KM_ELC_DEBUG_ITEMS=0 \
        KM_ELC_TIMING=1 \
        "$candidate_bin" elc \
    < "$clauses" > "$run_root/elc.json" 2> "$run_root/elc.stderr"
elc_rc=$?
set -e
worker_finished=$(/usr/bin/date --iso-8601=seconds)

# The current debug line exposes batch size and the first conflict tuple, but
# not the helper's global-bottom/local-dead/fallback tier. Compare against the
# exact capsule-04 pass baseline and state that attribution limit explicitly.
/usr/bin/python3 - \
    "$run_root/elc.stderr" "$elc_rc" "$run_root/batch-progress-summary.json" <<'PY'
from collections import Counter
import json
from pathlib import Path
import re
import sys

stderr_path = Path(sys.argv[1])
worker_rc = int(sys.argv[2])
output_path = Path(sys.argv[3])
lines = stderr_path.read_text(encoding="utf-8", errors="replace").splitlines()

batch_re = re.compile(
    r"repair pass (\d+): witness (\d+) .*? batching (\d+) choices "
    r"\(first \((\d+), (\d+), (\d+)\)\)"
)
broad_progress_re = re.compile(
    r"model cover seed (\d+): alive=(\d+) new=(\d+) "
    r"remaining_unwitnessed=(\d+) undetermined_pairs=(\d+)"
)
broad_no_model_re = re.compile(r"model cover seed (\d+): no checked model")
target_start_re = re.compile(r"targeted cover (\d+): protect id=(\d+) .* avoid=(.*)$")
target_progress_re = re.compile(
    r"targeted cover (\d+): alive=(\d+) new=(\d+) "
    r"remaining_unwitnessed=(\d+) undetermined_pairs=(\d+)"
)
target_no_model_re = re.compile(r"targeted cover (\d+): no checked target model")
target_extra_re = re.compile(
    r"targeted cover (\d+) attempt (\d+): extra .* persists; banning (.*)$"
)
repeated_re = re.compile(r"targeted cover (\d+) attempt (\d+): repeated conflict")
final_re = re.compile(
    r"model cover declined after (\d+) checked models: "
    r"unwitnessed=(\d+) undetermined_pairs=(\d+)"
)

batches = []
broad_progress = []
broad_no_model = []
target_starts = []
target_progress = []
target_no_model = []
target_extra = []
repeated_conflicts = []
final_cover = None
repair_failures = []
for line in lines:
    match = batch_re.search(line)
    if match:
        pass_label, witness, size, node, clause, concept = map(int, match.groups())
        if pass_label >= 1000:
            batches.append({
                "pass": pass_label,
                "target_index": (pass_label - 1000) // 64,
                "attempt": (pass_label - 1000) % 64,
                "witness_id": witness,
                "size": size,
                "first_conflict": {
                    "node_id": node,
                    "clause_index": clause,
                    "concept_id": concept,
                },
            })
        continue
    match = broad_progress_re.search(line)
    if match:
        broad_progress.append({
            "seed": int(match.group(1)),
            "alive": int(match.group(2)),
            "new": int(match.group(3)),
            "remaining_unwitnessed": int(match.group(4)),
            "undetermined_pairs": int(match.group(5)),
        })
        continue
    match = broad_no_model_re.search(line)
    if match:
        broad_no_model.append(int(match.group(1)))
        continue
    match = target_start_re.search(line)
    if match:
        target_starts.append({
            "index": int(match.group(1)),
            "target_id": int(match.group(2)),
            "avoid": match.group(3),
        })
        continue
    match = target_progress_re.search(line)
    if match:
        target_progress.append({
            "index": int(match.group(1)),
            "alive": int(match.group(2)),
            "new": int(match.group(3)),
            "remaining_unwitnessed": int(match.group(4)),
            "undetermined_pairs": int(match.group(5)),
        })
        continue
    match = target_no_model_re.search(line)
    if match:
        target_no_model.append(int(match.group(1)))
        continue
    match = target_extra_re.search(line)
    if match:
        target_extra.append({
            "target_index": int(match.group(1)),
            "attempt": int(match.group(2)),
            "banned": match.group(3),
        })
        continue
    match = repeated_re.search(line)
    if match:
        repeated_conflicts.append({
            "target_index": int(match.group(1)),
            "attempt": int(match.group(2)),
        })
        continue
    match = final_re.search(line)
    if match:
        final_cover = {
            "checked_models": int(match.group(1)),
            "unwitnessed": int(match.group(2)),
            "undetermined_pairs": int(match.group(3)),
        }
    if "KM_ELC_CERT repair fail:" in line:
        repair_failures.append(line)

sizes = [event["size"] for event in batches]
size_counts = Counter(sizes)
first_node_counts = Counter(
    event["first_conflict"]["node_id"] for event in batches
)
repeated_nodes = {
    str(node): count for node, count in sorted(first_node_counts.items()) if count > 1
}

baseline_multi_sizes = {
    1000: 328,
    1001: 177,
    1002: 140,
    1003: 64,
    1004: 45,
    1005: 42,
    1006: 10,
    1007: 11,
    1008: 10,
    1009: 5,
    1010: 6,
}
baseline_singleton_passes = list(range(1011, 1064))
current_by_pass = {event["pass"]: event["size"] for event in batches}
former_singletons_now_multi = {
    str(label): current_by_pass[label]
    for label in baseline_singleton_passes
    if current_by_pass.get(label, 0) > 1
}
former_singletons_still_single = [
    label for label in baseline_singleton_passes if current_by_pass.get(label) == 1
]
former_singletons_missing = [
    label for label in baseline_singleton_passes if label not in current_by_pass
]
baseline_multi_delta = {
    str(label): {
        "baseline_size": baseline_size,
        "current_size": current_by_pass.get(label),
        "delta": (
            current_by_pass[label] - baseline_size if label in current_by_pass else None
        ),
    }
    for label, baseline_size in baseline_multi_sizes.items()
}

record = {
    "schema_version": 2,
    "purpose": "non-acceptance capsule-05 protected-target batching diagnostic",
    "acceptance_evidence": False,
    "worker_return_code": worker_rc,
    "broad_cover": {
        "requested_models": 2,
        "checked_model_progress": broad_progress,
        "no_checked_model_seeds": broad_no_model,
    },
    "targeted_cover": {
        "requested_targets": 32,
        "restart_cap_per_target": 64,
        "starts": target_starts,
        "checked_model_progress": target_progress,
        "no_checked_model_targets": target_no_model,
        "extra_label_rejections": target_extra,
        "repeated_conflict_attempts": repeated_conflicts,
    },
    "observable_batches": {
        "events": len(batches),
        "sum_choices": sum(sizes),
        "min_size": min(sizes) if sizes else None,
        "max_size": max(sizes) if sizes else None,
        "singleton_sized_events": sum(size == 1 for size in sizes),
        "multi_choice_events": sum(size > 1 for size in sizes),
        "size_histogram": {
            str(size): count for size, count in sorted(size_counts.items())
        },
        "passes": batches,
    },
    "tier_attribution": {
        "directly_distinguishable": False,
        "global_bottom_sizes": None,
        "local_dead_sizes": None,
        "singleton_fallback_sizes": None,
        "reason": (
            "capsule-05 logs batch size and first conflict tuple but not the "
            "global-bottom, local-dead, or singleton-fallback return tier"
        ),
    },
    "capsule_04_baseline_comparison": {
        "baseline_job": 49209225,
        "baseline_driver_sha256": (
            "8ac514f90ce787b7bef488c4333f3b021366637ced75ef7da49fb8cf7d7421fa"
        ),
        "baseline_multi_pass_delta": baseline_multi_delta,
        "baseline_singleton_pass_range": [1011, 1063],
        "former_singletons_now_multi": former_singletons_now_multi,
        "former_singletons_still_single": former_singletons_still_single,
        "former_singletons_missing": former_singletons_missing,
    },
    "canonical_witness_sharing_proxy": {
        "metric": "repeated first-conflict node_id across protected-target batches",
        "caveat": (
            "the debug stream exposes only the first tuple in each batch; repeated "
            "node IDs are a proxy for sharing, not a proof of canonical identity"
        ),
        "first_conflict_node_histogram": {
            str(node): count for node, count in sorted(first_node_counts.items())
        },
        "repeated_first_conflict_nodes": repeated_nodes,
    },
    "final_cover": final_cover,
    "repair_failures": repair_failures,
}
tmp = Path(str(output_path) + ".tmp")
tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
tmp.replace(output_path)
print(json.dumps(record, sort_keys=True))
PY

ofn_peak_kib=$(/usr/bin/awk -F: \
    '/Maximum resident set size/ {gsub(/[[:space:]]/, "", $2); print $2}' \
    "$run_root/ofn.time")
elc_peak_kib=$(/usr/bin/awk -F: \
    '/Maximum resident set size/ {gsub(/[[:space:]]/, "", $2); print $2}' \
    "$run_root/elc.time")
[[ $ofn_peak_kib =~ ^[0-9]+$ ]]
[[ $elc_peak_kib =~ ^[0-9]+$ ]]
summary_sha256=$(sha_of "$run_root/batch-progress-summary.json")

/usr/bin/python3 - \
    "$run_root/non-acceptance-evidence.json" "$elc_rc" \
    "$diagnostic_driver_expected_sha256" "$summary_sha256" <<'PY'
import json
from pathlib import Path
import sys

record = {
    "schema_version": 1,
    "ontology": 10621,
    "purpose": "search diagnostic only",
    "acceptance_evidence": False,
    "taxonomy_validation_performed": False,
    "worker_return_code": int(sys.argv[2]),
    "diagnostic_driver_sha256": sys.argv[3],
    "batch_progress_summary_sha256": sys.argv[4],
    "reason": "this direct worker trace deliberately performs no oracle comparison",
}
Path(sys.argv[1]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
PY

{
    echo "job_id=$SLURM_JOB_ID"
    echo "host=$(/usr/bin/hostname)"
    echo "cpu_model=$cpu_model"
    echo "purpose=non-acceptance capsule-05 protected-target batching diagnostic"
    echo "acceptance_evidence=false"
    echo "frontend_started=$frontend_started"
    echo "frontend_finished=$frontend_finished"
    echo "frontend_return_code=$ofn_rc"
    echo "frontend_command=/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C KM_ROUTE=elc_cert $candidate_bin ofn $ontology --meta $meta > $clauses"
    echo "worker_started=$worker_started"
    echo "worker_finished=$worker_finished"
    echo "worker_return_code=$elc_rc"
    echo "worker_command=/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C KM_ELC_CERT=2 KM_ELC_COVER_MODELS=2 KM_ELC_TARGET_MODELS=32 KM_ELC_TARGET_RESTARTS=64 KM_ELC_DEBUG=1 KM_ELC_DEBUG_ITEMS=0 KM_ELC_TIMING=1 $candidate_bin elc < $clauses"
    echo "diagnostic_lower=absent_from_env_i"
    echo "clauses_sha256=$clauses_sha256"
    echo "meta_sha256=$meta_sha256"
    echo "batch_progress_summary_sha256=$summary_sha256"
    echo "ofn_maximum_resident_kib=$ofn_peak_kib"
    echo "elc_maximum_resident_kib=$elc_peak_kib"
    echo "timeout_seconds=240"
    echo "slurm_cpus=$SLURM_CPUS_PER_TASK"
    echo "slurm_memory=20G"
    echo "diagnostic_driver_sha256=$diagnostic_driver_expected_sha256"
    echo "capsule_core_stream_sha256=$core_stream_sha256"
    echo "km_sha256=$candidate_expected_sha256"
    echo "source_archive_sha256=$source_archive_expected_sha256"
    echo "source_manifest_sha256=$source_manifest_expected_sha256"
    echo "build_input_archive_sha256=$build_input_archive_expected_sha256"
    echo "build_input_manifest_sha256=$build_input_manifest_expected_sha256"
    echo "build_receipt_sha256=$build_receipt_expected_sha256"
    echo "ontology_sha256=$ontology_expected_sha256"
} > "$run_root/run.meta"

/usr/bin/sha256sum \
    "$run_root/inputs.sha256" "$run_root/core-files.sha256" \
    "$run_root/core-check.json" "$run_root/build-receipt-check.json" \
    "$run_root/frontend.sha256" "$run_root/frontend-check.json" \
    "$run_root/invocations.json" "$run_root/batch-progress-summary.json" \
    "$run_root/non-acceptance-evidence.json" "$clauses" "$meta" \
    "$run_root/ofn.stderr" "$run_root/ofn.time" \
    "$run_root/elc.json" "$run_root/elc.stderr" "$run_root/elc.time" \
    "$run_root/run.meta" > "$run_root/outputs.sha256"

# These are diagnostic completion codes only. Even rc=0 cannot establish a
# solve because this driver deliberately performs no taxonomy comparison.
case "$elc_rc" in
    0|3|4|124) ;;
    *) exit "$elc_rc" ;;
esac
/usr/bin/printf \
    'TRACE_COMPLETE acceptance_evidence=false elc_rc=%s run_root=%s\n' \
    "$elc_rc" "$run_root"
