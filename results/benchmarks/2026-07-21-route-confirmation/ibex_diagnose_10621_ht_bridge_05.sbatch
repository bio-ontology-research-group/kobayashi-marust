#!/bin/bash
# NON-ACCEPTANCE DIAGNOSTIC for capsule-05 on ORE 10621.
#
# This driver asks the exact named ht_bridge route to expose its current
# boundary.  It records the cb_to_ht TInput, route guards, bridge coverage,
# first unsupported clause shapes, saturation/completion progress, and a hard
# 30-second process cap.  It deliberately performs no taxonomy/oracle
# comparison.  Even a zero exit code is acceptance_evidence=false.
#
# Review/stage only; do not submit from this checkout.  On IBEX, copy this file
# unchanged to:
#   diagnostic-drivers/sha256-$(sha256sum FILE | awk '{print $1}')/
# and submit from that hash-named directory so the self-hash gate is effective.
#SBATCH --job-name=km10621-bridge05-diag
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:06:00
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
diagnostic_driver=$submit_dir_canonical/ibex_diagnose_10621_ht_bridge_05.sbatch

ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl
ontology_expected_sha256=5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167
run_root=/ibex/scratch/hohndor/km/routing_20260715/10621-ht-bridge-05-${SLURM_JOB_ID}
unsupported_dump_cap=8192
process_timeout_seconds=30

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
    "$build_receipt" "$run_root/build-receipt-check.json" <<'PY'
import json
from pathlib import Path
import re
import sys

receipt = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
output = Path(sys.argv[2])
build = receipt.get("build", {})
build_input = receipt.get("build_input", {})
container = receipt.get("container", {})
outputs = receipt.get("outputs", {})
source = receipt.get("source", {})
toolchain = receipt.get("toolchain", {})
binary = "7f5e39ac7e989ca7f029090d051f009a8b2f2da5d410aeccc376d9630143c0bf"
checks = {
    "status_verified_reproducible": receipt.get("status") == "verified_reproducible",
    "byte_identical": outputs.get("byte_identical") is True,
    "binary_hash": outputs.get("binary_sha256") == binary,
    "build_a_hash": outputs.get("build_a_sha256") == binary,
    "build_b_hash": outputs.get("build_b_sha256") == binary,
    "source_archive": source.get("archive_sha256")
    == "91150f63f596e188ceae6a55f19acd0a5a9521f059cc86f0d3dc0dfee4c85f52",
    "source_manifest": source.get("manifest_sha256")
    == "d5713b963d98f420939bf3843059e9edcbe06fd8c008536fee1e98202a7bf86e",
    "source_count": source.get("manifest_file_count") == 272,
    "cargo_lock": source.get("cargo_lock_sha256")
    == "f984323988b157fe566fb3d9a92c14b152820ad60631f3a9c1c3d5db9abc890b",
    "build_input_archive": build_input.get("archive_sha256")
    == "ceb06be141d847cba12dbdc987d3c4f585afbc9b2d4c2d4cb7aeea1c3546a793",
    "build_input_manifest": build_input.get("manifest_sha256")
    == "5db9089f5663288b3b4ba1ca603e45fa7c144f2b885af1d455c7853b387aaea4",
    "build_input_count": build_input.get("manifest_file_count") == 4234,
    "vendored_input": build_input.get("includes_vendored_dependencies") is True,
    "build_command": build.get("command")
    == ["cargo", "build", "--release", "--locked", "--offline", "-j4", "--bin", "km"],
    "build_limits": build.get("cpus") == 4
    and build.get("jobs") == 4
    and build.get("memory_gib") == 16,
    "locked_offline": build.get("cargo_locked") is True
    and build.get("offline_vendored") is True
    and build.get("network_disabled") is True,
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
tmp = Path(str(output) + ".tmp")
tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
tmp.replace(output)
if record["status"] != "ok":
    raise SystemExit(1)
PY

tin=$run_root/10621.ht-bridge.tin.json
route_stdout=$run_root/ht-bridge.stdout
route_stderr=$run_root/ht-bridge.stderr
route_started=$(/usr/bin/date --iso-8601=seconds)
set +e
/usr/bin/time -v -o "$run_root/ht-bridge.time" \
    /usr/bin/timeout -k 5 "$process_timeout_seconds" \
    /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
        KM_DUMP_TIN="$tin" \
        KM_HT_STATS=1 \
        KM_BRIDGE_PROGRESS=1 \
        KM_BRIDGE_DUMP_UNSUP="$unsupported_dump_cap" \
        KM_TIMING=1 \
        "$candidate_bin" classify --route ht_bridge "$ontology" \
    > "$route_stdout" 2> "$route_stderr"
route_rc=$?
set -e
route_finished=$(/usr/bin/date --iso-8601=seconds)

/usr/bin/python3 - \
    "$run_root/invocation.json" "$candidate_bin" "$candidate_expected_sha256" \
    "$ontology" "$ontology_expected_sha256" "$tin" \
    "$diagnostic_driver_expected_sha256" "$process_timeout_seconds" \
    "$unsupported_dump_cap" <<'PY'
import json
from pathlib import Path
import sys

record = {
    "schema_version": 1,
    "purpose": "capsule-05 ORE 10621 ht_bridge decline diagnostic",
    "acceptance_evidence": False,
    "taxonomy_validation_performed": False,
    "diagnostic_driver_sha256": sys.argv[7],
    "binary_sha256": sys.argv[3],
    "ontology_sha256": sys.argv[5],
    "command": [
        "/usr/bin/timeout", "-k", "5", sys.argv[8],
        "/usr/bin/env", "-i", "PATH=/usr/bin:/bin", "LC_ALL=C",
        f"KM_DUMP_TIN={sys.argv[6]}", "KM_HT_STATS=1",
        "KM_BRIDGE_PROGRESS=1", f"KM_BRIDGE_DUMP_UNSUP={sys.argv[9]}",
        "KM_TIMING=1", sys.argv[2], "classify", "--route", "ht_bridge", sys.argv[4],
    ],
    "environment": {
        "LC_ALL": "C",
        "KM_BRIDGE_DUMP_UNSUP": sys.argv[9],
        "KM_BRIDGE_PROGRESS": "1",
        "KM_DUMP_TIN": sys.argv[6],
        "KM_HT_STATS": "1",
        "KM_TIMING": "1",
        "PATH": "/usr/bin:/bin",
    },
    # `--route ht_bridge` normalizes these hidden KM_* keys in
    # routing.rs::Route::apply_environment before the frontend runs.  Record
    # the semantic bundle, not just the five diagnostic variables supplied to
    # env(1), so the TInput and worker configuration are reproducible.
    "normalized_named_route_bundle": {
        "KM_ABSORB": "0",
        "KM_BRIDGE_PROBE_BUDGET_S": "30",
        "KM_BRIDGE_RETRY_ROUNDS": "0",
        "KM_HT_MEM_GB": "18",
        "KM_HT_NICE": "0",
        "KM_HT_ONLY": "bridge",
        "KM_HT_SATURATION_BUDGET_S": "180",
        "KM_KEEP_CHAIN_AXIOMS": "1",
        "KM_MECHANISM": "ht",
        "KM_NO_ABSORB_PORTFOLIO": "1",
        "KM_NO_ELC": "1",
        "KM_NO_HT_CARD": "1",
        "KM_NO_HT_QO_ROUTER": "1",
        "KM_NO_HT_RULES": "1",
        "KM_NO_HT_SHOQ": "1",
        "KM_PAR_MEM_GB": "18",
        "KM_THREADS": "16",
        "KM_TRIGGER_ABSORB": "1",
    },
    "explicitly_absent": ["KM_HT_FORCE", "KM_NOMINALS"],
    "limits": {
        "timeout_seconds": int(sys.argv[8]),
        "slurm_cpus": 16,
        "slurm_memory": "20G",
    },
}
Path(sys.argv[1]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
PY

/usr/bin/python3 - \
    "$route_stderr" "$tin" "$route_rc" "$unsupported_dump_cap" \
    "$run_root/ht-bridge-summary.json" <<'PY'
from collections import Counter
import json
from pathlib import Path
import re
import sys

stderr_path = Path(sys.argv[1])
tin_path = Path(sys.argv[2])
route_rc = int(sys.argv[3])
dump_cap = int(sys.argv[4])
output = Path(sys.argv[5])
lines = stderr_path.read_text(encoding="utf-8", errors="replace").splitlines()

dump_line = next((line for line in lines if line.startswith("KM_DUMP_TIN ")), None)
source_line = next((line for line in lines if line.startswith("bridge [source-tbox] ")), None)
source_match = re.search(r"unsupported=(\d+)$", source_line or "")
source_unsupported = int(source_match.group(1)) if source_match else None
unsupported_lines = [line for line in lines if line.startswith("UNSUP[")]
unsupported_reasons = Counter()
for line in unsupported_lines:
    match = re.match(r"UNSUP\[([^]]+)\]", line)
    unsupported_reasons[match.group(1) if match else "unparsed"] += 1

tin = None
tin_error = None
if tin_path.is_file() and tin_path.stat().st_size:
    try:
        tin = json.loads(tin_path.read_text(encoding="utf-8"))
    except Exception as exc:  # diagnostic artifact; preserve the parse failure
        tin_error = f"{type(exc).__name__}: {exc}"

tin_summary = None
invalid_reference_count = None
if isinstance(tin, dict):
    concepts = tin.get("concepts", [])
    roles = tin.get("roles", [])
    invalid = []
    # bridge_tinput combines chains with transitivity-as-(R,R,R), sorts, and
    # deduplicates before counting invalid triples. Mirror that exact operation
    # so one invalid transitive role cannot be appended/counted twice.
    role_chains = set()
    malformed_chains = []
    for value in tin.get("chains", []):
        if not isinstance(value, (list, tuple)) or len(value) != 3:
            malformed_chains.append(value)
        else:
            role_chains.add(tuple(value))
    for value in tin.get("transitive", []):
        role_chains.add((value, value, value))
    invalid.extend(["chains", value] for value in malformed_chains)
    for value in sorted(role_chains, key=repr):
        if any(not isinstance(x, int) or x < 0 or x >= len(roles) for x in value):
            invalid.append(["role_chain", list(value)])
    for field in ("role_domains", "role_ranges"):
        for value in tin.get(field, []):
            if (len(value) != 2 or not isinstance(value[0], int)
                    or not isinstance(value[1], int) or value[0] < 0
                    or value[0] >= len(roles) or value[1] < 0
                    or value[1] >= len(concepts)):
                invalid.append([field, value])
    invalid_reference_count = len(invalid)
    tin_summary = {
        "bytes": tin_path.stat().st_size,
        "concepts": len(concepts),
        "roles": len(roles),
        "clauses": len(tin.get("clauses", [])),
        "queries": len(tin.get("queries", [])),
        "dropped": tin.get("dropped"),
        "fenced_count": len(tin.get("fenced", [])),
        "fenced": tin.get("fenced", []),
        "nominals_count": len(tin.get("nominals", [])),
        "inverse": tin.get("inverse"),
        "number": tin.get("number"),
        "card_defs": len(tin.get("card_defs", [])),
        "chains": len(tin.get("chains", [])),
        "transitive": len(tin.get("transitive", [])),
        "role_domains": len(tin.get("role_domains", [])),
        "role_ranges": len(tin.get("role_ranges", [])),
        "definers": len(tin.get("definers", [])),
        "source_axioms": len(tin.get("source_axioms", [])),
        "negative_existential_defs": len(tin.get("negative_existential_defs", [])),
        "negative_existential_proxy_source_safe": tin.get(
            "negative_existential_proxy_source_safe"
        ),
        "invalid_reference_count": invalid_reference_count,
        "invalid_references_first_32": invalid[:32],
    }

route_gate = None
if tin_summary is not None:
    # Named ht_bridge sets KM_TRIGGER_ABSORB=1 and does not set
    # KM_NO_SOURCE_TBOX. This is the exact `source_tbox` expression in
    # orchestrate/race.rs. bridge_fences_supported accepts the two native
    # inverse/cardinality fences unconditionally and complex domain/range only
    # in this source-TBox mode.
    source_mode = tin_summary["source_axioms"] > 0
    allowed_fence_reasons = {
        "inverse+number(SHIQ)",
        "inverse-functional",
    }
    if source_mode:
        allowed_fence_reasons.update({"complex-domain", "complex-range"})
    blocking_fences = [
        fence
        for fence in tin_summary["fenced"]
        if not isinstance(fence, dict)
        or fence.get("reason") not in allowed_fence_reasons
    ]
    blockers = []
    if tin_summary["dropped"] != 0:
        blockers.append("dropped")
    if blocking_fences:
        blockers.append("unsupported-fence")
    if tin_summary["nominals_count"] != 0:
        blockers.append("nominals")
    route_gate = {
        "trigger_bridge": True,
        "source_mode": source_mode,
        "allowed_fence_reasons": sorted(allowed_fence_reasons),
        "blocking_fences": blocking_fences,
        "bridge_candidate_preconditions_pass": not blockers,
        "blocking_fields": blockers,
    }

# bridge_tinput's non-clause unsupported terms are nominals, invalid generated
# RBox references, and source-TBox encodings. Every remaining clause-scan
# rejection emits one UNSUP line. The reconstruction is exact only when the
# worker reached source mode and the dump did not hit its cap.
nominals = tin_summary["nominals_count"] if tin_summary is not None else None
reconstructable = (
    source_unsupported is not None
    and nominals is not None
    and invalid_reference_count is not None
    and len(unsupported_lines) < dump_cap
)
unsupported_total = None
if reconstructable:
    unsupported_total = (
        source_unsupported + nominals + invalid_reference_count + len(unsupported_lines)
    )

progress_prefixes = (
    "BRIDGE-", "SAT-STATS:", "PROGRESS-SAT", "HT-STATS", "KM_TIMING"
)
progress = [line for line in lines if line.startswith(progress_prefixes)]
record = {
    "schema_version": 2,
    "purpose": "capsule-05 ORE 10621 ht_bridge decline diagnostic",
    "acceptance_evidence": False,
    "taxonomy_validation_performed": False,
    "route_return_code": route_rc,
    "timed_out_at_30_seconds": route_rc == 124,
    "dump_line": dump_line,
    "tin_error": tin_error,
    "tin": tin_summary,
    "route_gate": route_gate,
    "bridge_coverage": {
        "source_stats_line": source_line,
        "source_unsupported": source_unsupported,
        "clause_unsupported_lines": len(unsupported_lines),
        "dump_cap": dump_cap,
        "dump_truncated": len(unsupported_lines) >= dump_cap,
        "reason_histogram": dict(sorted(unsupported_reasons.items())),
        "first_unsupported_shapes": unsupported_lines[:32],
        "total_reconstructable": reconstructable,
        "reconstructed_total_unsupported": unsupported_total,
        "reconstruction_formula": (
            "source_unsupported + tin.nominals + invalid_generated_rbox_refs "
            "+ clause_scan_UNSUP_lines"
        ),
    },
    "progress_lines": progress[:512],
    "stderr_line_count": len(lines),
}
tmp = Path(str(output) + ".tmp")
tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
tmp.replace(output)
print(json.dumps(record, sort_keys=True))
PY

route_peak_kib=$(/usr/bin/awk -F: \
    '/Maximum resident set size/ {gsub(/[[:space:]]/, "", $2); print $2}' \
    "$run_root/ht-bridge.time")
[[ $route_peak_kib =~ ^[0-9]+$ ]]
summary_sha256=$(sha_of "$run_root/ht-bridge-summary.json")
tin_sha256=absent
if /usr/bin/test -s "$tin"; then
    tin_sha256=$(sha_of "$tin")
fi

/usr/bin/python3 - \
    "$run_root/non-acceptance-evidence.json" "$route_rc" \
    "$diagnostic_driver_expected_sha256" "$summary_sha256" <<'PY'
import json
from pathlib import Path
import sys

record = {
    "schema_version": 1,
    "ontology": 10621,
    "purpose": "ht_bridge decline diagnostic only",
    "acceptance_evidence": False,
    "taxonomy_validation_performed": False,
    "route_return_code": int(sys.argv[2]),
    "diagnostic_driver_sha256": sys.argv[3],
    "summary_sha256": sys.argv[4],
    "reason": (
        "the route is capped at 30 seconds and no taxonomy/oracle comparison "
        "is performed; any stdout is non-acceptance diagnostic material"
    ),
}
Path(sys.argv[1]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
PY

{
    echo "job_id=$SLURM_JOB_ID"
    echo "host=$(/usr/bin/hostname)"
    echo "cpu_model=$cpu_model"
    echo "purpose=capsule-05 ORE 10621 ht_bridge decline diagnostic"
    echo "acceptance_evidence=false"
    echo "taxonomy_validation_performed=false"
    echo "route_started=$route_started"
    echo "route_finished=$route_finished"
    echo "route_return_code=$route_rc"
    echo "route_command=/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C KM_DUMP_TIN=$tin KM_HT_STATS=1 KM_BRIDGE_PROGRESS=1 KM_BRIDGE_DUMP_UNSUP=$unsupported_dump_cap KM_TIMING=1 $candidate_bin classify --route ht_bridge $ontology"
    echo "timeout_seconds=$process_timeout_seconds"
    echo "route_maximum_resident_kib=$route_peak_kib"
    echo "tin_sha256=$tin_sha256"
    echo "summary_sha256=$summary_sha256"
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

{
    for artifact in \
        "$run_root/inputs.sha256" "$run_root/core-files.sha256" \
        "$run_root/build-receipt-check.json" "$run_root/invocation.json" \
        "$run_root/ht-bridge-summary.json" \
        "$run_root/non-acceptance-evidence.json" \
        "$route_stdout" "$route_stderr" "$run_root/ht-bridge.time" \
        "$run_root/run.meta" "$tin"; do
        if /usr/bin/test -e "$artifact"; then
            /usr/bin/sha256sum "$artifact"
        fi
    done
} > "$run_root/outputs.sha256"

/usr/bin/printf \
    'TRACE_COMPLETE acceptance_evidence=false route_rc=%s run_root=%s\n' \
    "$route_rc" "$run_root"
