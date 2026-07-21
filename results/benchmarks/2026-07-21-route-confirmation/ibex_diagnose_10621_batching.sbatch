#!/bin/bash
# NON-ACCEPTANCE DIAGNOSTIC for ORE 10621.
#
# Exposes only the protected-target batch sizes and model-cover progress of the
# final reproducible candidate.  This driver never fingerprints or accepts a
# taxonomy.  Every artifact is explicitly marked acceptance_evidence=false.
#SBATCH --job-name=km10621-batch-diag
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
export LC_ALL=C

candidate_bin=${KM_BIN:?exact reproducible-capsule binary}
candidate_expected_sha256=${KM_EXPECTED_SHA256:?expected SHA-256 of KM_BIN}
source_archive=${SOURCE_ARCHIVE:?source snapshot used by the build}
source_archive_expected_sha256=${SOURCE_ARCHIVE_EXPECTED_SHA256:?expected source archive SHA-256}
source_manifest=${SOURCE_MANIFEST:?per-file source manifest}
source_manifest_expected_sha256=${SOURCE_MANIFEST_EXPECTED_SHA256:?expected source manifest SHA-256}
build_receipt=${BUILD_PROVENANCE:?reproducible-build receipt}
build_receipt_expected_sha256=${BUILD_PROVENANCE_EXPECTED_SHA256:?expected build receipt SHA-256}
diagnostic_driver=${DIAGNOSTIC_DRIVER:?immutable submitted diagnostic driver}
diagnostic_driver_expected_sha256=${DIAGNOSTIC_DRIVER_EXPECTED_SHA256:?expected driver SHA-256}
ontology=${ONTOLOGY:-/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl}
ontology_expected_sha256=${ONTOLOGY_EXPECTED_SHA256:-5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167}
run_root=${RUN_ROOT:-/ibex/scratch/hohndor/km/routing_20260715/10621-batch-diagnostic-${SLURM_JOB_ID}}

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

/usr/bin/test -x "$candidate_bin"
for input in \
    "$source_archive" "$source_manifest" "$build_receipt" \
    "$diagnostic_driver" "$ontology"; do
    /usr/bin/test -s "$input"
done
/usr/bin/test "$(sha_of "$candidate_bin")" = "$candidate_expected_sha256"
/usr/bin/test "$(sha_of "$source_archive")" = "$source_archive_expected_sha256"
/usr/bin/test "$(sha_of "$source_manifest")" = "$source_manifest_expected_sha256"
/usr/bin/test "$(sha_of "$build_receipt")" = "$build_receipt_expected_sha256"
/usr/bin/test "$(sha_of "$diagnostic_driver")" = "$diagnostic_driver_expected_sha256"
/usr/bin/test "$(sha_of "$ontology")" = "$ontology_expected_sha256"

/usr/bin/mkdir -p "$run_root"
/usr/bin/sha256sum \
    "$candidate_bin" "$source_archive" "$source_manifest" "$build_receipt" \
    "$diagnostic_driver" "$ontology" > "$run_root/inputs.sha256"

# Check that the receipt binds this exact candidate and source to two
# byte-identical locked/offline/network-isolated builds and resolved tools.
/usr/bin/python3 - \
    "$build_receipt" "$candidate_expected_sha256" \
    "$source_archive_expected_sha256" "$source_manifest_expected_sha256" \
    "$run_root/build-receipt-check.json" <<'PY'
import json
from pathlib import Path
import re
import sys

receipt = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
candidate_sha, archive_sha, manifest_sha = sys.argv[2:5]
output_path = Path(sys.argv[5])
build = receipt.get("build", {})
outputs = receipt.get("outputs", {})
source = receipt.get("source", {})
container = receipt.get("container", {})
toolchain = receipt.get("toolchain", {})
match = re.search(
    r"(?m)^commit-hash:\s*([0-9a-f]{40})$",
    toolchain.get("rustc_version_verbose", ""),
)
rustc_commit = toolchain.get("rustc_commit") or (match.group(1) if match else None)
container_digest = container.get("image_digest")
tool_hashes = {
    toolchain.get("rustc_sha256"),
    toolchain.get("cargo_sha256"),
    toolchain.get("rustup_sha256"),
}
checks = {
    "status_verified_reproducible": receipt.get("status") == "verified_reproducible",
    "byte_identical": outputs.get("byte_identical") is True,
    "binary_hash": outputs.get("binary_sha256") == candidate_sha,
    "build_a_hash": outputs.get("build_a_sha256") == candidate_sha,
    "build_b_hash": outputs.get("build_b_sha256") == candidate_sha,
    "source_archive_hash": source.get("archive_sha256") == archive_sha,
    "source_manifest_hash": source.get("manifest_sha256") == manifest_sha,
    "cargo_locked": build.get("cargo_locked") is True,
    "offline_vendored": build.get("offline_vendored") is True,
    "network_disabled": build.get("network_disabled") is True,
    "container_digest_present": isinstance(container_digest, str)
    and bool(re.fullmatch(r"sha256:[0-9a-f]{64}", container_digest)),
    "rustc_commit_present": isinstance(rustc_commit, str)
    and bool(re.fullmatch(r"[0-9a-f]{40}", rustc_commit)),
    "resolved_rustc_hash": bool(toolchain.get("rustc_path"))
    and bool(toolchain.get("rustc_sha256")),
    "resolved_cargo_hash": bool(toolchain.get("cargo_path"))
    and bool(toolchain.get("cargo_sha256")),
    "rustup_dispatcher_hash": bool(toolchain.get("rustup_path"))
    and bool(toolchain.get("rustup_sha256")),
    "distinct_resolved_tool_hashes": None not in tool_hashes
    and len(tool_hashes) == 3,
}
record = {
    "schema_version": 1,
    "status": "ok" if all(checks.values()) else "mismatch",
    "checks": checks,
    "candidate_sha256": candidate_sha,
    "source_archive_sha256": archive_sha,
    "source_manifest_sha256": manifest_sha,
    "container_digest": container_digest,
    "rustc_commit": rustc_commit,
}
tmp = Path(str(output_path) + ".tmp")
tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
tmp.replace(output_path)
if record["status"] != "ok":
    raise SystemExit(1)
PY

clauses=$run_root/clauses.json
meta=$run_root/meta.json
set +e
/usr/bin/time -v -o "$run_root/ofn.time" \
    /usr/bin/timeout -k 10 240 \
    /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
        KM_ROUTE=elc_cert KM_BOTTOM_PREPASS_STATS=1 \
        "$candidate_bin" ofn "$ontology" --meta "$meta" \
    > "$clauses" 2> "$run_root/ofn.stderr"
ofn_rc=$?
set -e
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
record = {
    "status": "ok" if meta.get("route") == "elc_cert" else "mismatch",
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
    "$run_root/worker-invocation.json" "$candidate_bin" "$candidate_expected_sha256" \
    "$clauses" "$clauses_sha256" "$meta" "$meta_sha256" \
    "$diagnostic_driver_expected_sha256" <<'PY'
import json
from pathlib import Path
import sys

record = {
    "schema_version": 1,
    "purpose": "non-acceptance protected-target batching diagnostic",
    "acceptance_evidence": False,
    "command": [sys.argv[2], "elc"],
    "binary_sha256": sys.argv[3],
    "stdin": sys.argv[4],
    "stdin_sha256": sys.argv[5],
    "frontend_meta": sys.argv[6],
    "frontend_meta_sha256": sys.argv[7],
    "diagnostic_driver_sha256": sys.argv[8],
    "environment": {
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "KM_ELC_CERT": "2",
        "KM_ELC_COVER_MODELS": "2",
        "KM_ELC_TARGET_MODELS": "32",
        "KM_ELC_TARGET_RESTARTS": "64",
        "KM_ELC_DEBUG": "1",
        "KM_ELC_DEBUG_ITEMS": "0",
        "KM_ELC_TIMING": "1",
    },
    "explicitly_absent": ["KM_ELC_DIAGNOSTIC_LOWER"],
    "timeout_seconds": 240,
    "slurm_cpus": 16,
    "slurm_memory": "20G",
}
Path(sys.argv[1]).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
PY

started=$(/usr/bin/date --iso-8601=seconds)
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
finished=$(/usr/bin/date --iso-8601=seconds)

# Reduce the debug stream to the information needed to choose the next source
# change.  Raw stderr remains retained and hashed.
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

batch_re = re.compile(r"repair pass (\d+): .* batching (\d+) choices")
broad_re = re.compile(
    r"model cover seed (\d+): alive=(\d+) new=(\d+) "
    r"remaining_unwitnessed=(\d+) undetermined_pairs=(\d+)"
)
target_start_re = re.compile(r"targeted cover (\d+): protect id=(\d+) .* avoid=(.*)$")
target_progress_re = re.compile(
    r"targeted cover (\d+): alive=(\d+) new=(\d+) "
    r"remaining_unwitnessed=(\d+) undetermined_pairs=(\d+)"
)
target_no_model_re = re.compile(r"targeted cover (\d+): no checked target model")
final_re = re.compile(
    r"model cover declined after (\d+) checked models: "
    r"unwitnessed=(\d+) undetermined_pairs=(\d+)"
)

target_batches = []
broad_progress = []
target_starts = []
target_progress = []
target_no_model = []
final_cover = None
repair_failures = []
for line in lines:
    match = batch_re.search(line)
    if match:
        pass_label = int(match.group(1))
        size = int(match.group(2))
        if pass_label >= 1000:
            target_batches.append({"pass": pass_label, "size": size})
        continue
    match = broad_re.search(line)
    if match:
        broad_progress.append({
            "seed": int(match.group(1)),
            "alive": int(match.group(2)),
            "new": int(match.group(3)),
            "remaining_unwitnessed": int(match.group(4)),
            "undetermined_pairs": int(match.group(5)),
        })
        continue
    match = target_start_re.search(line)
    if match:
        target_starts.append({
            "index": int(match.group(1)),
            "target_id": int(match.group(2)),
            "avoid": match.group(3),
            "line": line,
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
    match = final_re.search(line)
    if match:
        final_cover = {
            "checked_models": int(match.group(1)),
            "unwitnessed": int(match.group(2)),
            "undetermined_pairs": int(match.group(3)),
        }
    if "KM_ELC_CERT repair fail:" in line:
        repair_failures.append(line)

sizes = [item["size"] for item in target_batches]
size_counts = Counter(sizes)
batch_summary = {
    "events": len(sizes),
    "singleton_events": sum(size == 1 for size in sizes),
    "multi_choice_events": sum(size > 1 for size in sizes),
    "min": min(sizes) if sizes else None,
    "max": max(sizes) if sizes else None,
    "sum": sum(sizes),
    "sizes": {str(size): count for size, count in sorted(size_counts.items())},
    "passes": target_batches,
}
if batch_summary["multi_choice_events"]:
    attribution = "causal_multi_choice_batches_observed"
elif batch_summary["singleton_events"]:
    attribution = "singleton_fallback_only"
else:
    attribution = "no_protected_target_death_logged"

record = {
    "schema_version": 1,
    "purpose": "non-acceptance protected-target batching diagnostic",
    "acceptance_evidence": False,
    "worker_return_code": worker_rc,
    "attribution": attribution,
    "target_batch_summary": batch_summary,
    "broad_model_progress": broad_progress,
    "target_starts": target_starts,
    "target_model_progress": target_progress,
    "target_no_checked_model": target_no_model,
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

{
    echo "job_id=$SLURM_JOB_ID"
    echo "host=$(/usr/bin/hostname)"
    echo "purpose=non-acceptance protected-target batching diagnostic"
    echo "acceptance_evidence=false"
    echo "started=$started"
    echo "finished=$finished"
    echo "ofn_return_code=$ofn_rc"
    echo "elc_return_code=$elc_rc"
    echo "worker_command=$candidate_bin elc < $clauses"
    echo "worker_environment=KM_ELC_CERT=2,KM_ELC_COVER_MODELS=2,KM_ELC_TARGET_MODELS=32,KM_ELC_TARGET_RESTARTS=64,KM_ELC_DEBUG=1,KM_ELC_DEBUG_ITEMS=0,KM_ELC_TIMING=1"
    echo "clauses_sha256=$clauses_sha256"
    echo "meta_sha256=$meta_sha256"
    echo "batch_progress_summary_sha256=$summary_sha256"
    echo "ofn_maximum_resident_kib=$ofn_peak_kib"
    echo "elc_maximum_resident_kib=$elc_peak_kib"
    echo "timeout_seconds=240"
    echo "slurm_cpus=$SLURM_CPUS_PER_TASK"
    echo "slurm_memory=20G"
    echo "diagnostic_lower=absent_from_env_i"
    echo "diagnostic_driver_sha256=$diagnostic_driver_expected_sha256"
    echo "km_sha256=$candidate_expected_sha256"
    echo "source_archive_sha256=$source_archive_expected_sha256"
    echo "source_manifest_sha256=$source_manifest_expected_sha256"
    echo "build_receipt_sha256=$build_receipt_expected_sha256"
    echo "ontology_sha256=$ontology_expected_sha256"
} > "$run_root/run.meta"

/usr/bin/sha256sum \
    "$run_root/build-receipt-check.json" "$run_root/frontend.sha256" \
    "$run_root/frontend-check.json" "$run_root/worker-invocation.json" \
    "$run_root/batch-progress-summary.json" "$clauses" "$meta" \
    "$run_root/ofn.stderr" "$run_root/ofn.time" \
    "$run_root/elc.json" "$run_root/elc.stderr" "$run_root/elc.time" \
    "$run_root/run.meta" > "$run_root/outputs.sha256"

# These are diagnostic completion codes only.  Even rc=0 cannot establish a
# solve because this driver deliberately performs no taxonomy comparison.
case "$elc_rc" in
    0|3|4|124) ;;
    *) exit "$elc_rc" ;;
esac
/usr/bin/printf \
    'TRACE_COMPLETE acceptance_evidence=false elc_rc=%s run_root=%s\n' \
    "$elc_rc" "$run_root"
