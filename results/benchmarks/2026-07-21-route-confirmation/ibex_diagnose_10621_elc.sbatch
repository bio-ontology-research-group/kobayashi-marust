#!/bin/bash
# NON-ACCEPTANCE DIAGNOSTIC for ORE 10621.
#
# This job exposes certificate-search residue by running the pinned frontend
# and ELC worker directly.  Its output MUST NOT be used as route-validation or
# soundness/completeness evidence.  Only ibex_validate_10621_fulliri.sbatch can
# produce acceptance evidence, and that job requires an exact Konclude match.
#SBATCH --job-name=km10621-elc-diag
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
ontology=${ONTOLOGY:-/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl}
ontology_expected_sha256=${ONTOLOGY_EXPECTED_SHA256:-5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167}
run_root=${RUN_ROOT:-/ibex/scratch/hohndor/km/routing_20260715/10621-elc-diagnostic-${SLURM_JOB_ID}}

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

/usr/bin/test -x "$candidate_bin"
/usr/bin/test -s "$source_archive"
/usr/bin/test -s "$source_manifest"
/usr/bin/test -s "$build_receipt"
/usr/bin/test -s "$ontology"
/usr/bin/test "$(sha_of "$candidate_bin")" = "$candidate_expected_sha256"
/usr/bin/test "$(sha_of "$source_archive")" = "$source_archive_expected_sha256"
/usr/bin/test "$(sha_of "$source_manifest")" = "$source_manifest_expected_sha256"
/usr/bin/test "$(sha_of "$build_receipt")" = "$build_receipt_expected_sha256"
/usr/bin/test "$(sha_of "$ontology")" = "$ontology_expected_sha256"

/usr/bin/mkdir -p "$run_root"
/usr/bin/sha256sum \
    "$candidate_bin" "$source_archive" "$source_manifest" "$build_receipt" \
    "$ontology" > "$run_root/inputs.sha256"

# Recheck the same internal receipt bindings as the decisive validator.  This
# prevents a useful-looking trace from being attributed to an opaque binary.
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
}
record = {
    "schema_version": 1,
    "status": "ok" if all(checks.values()) else "mismatch",
    "checks": checks,
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

# `KM_ROUTE=elc_cert` makes the frontend install the same named route before
# normalization.  A clean environment prevents inherited experimental flags
# from changing the pinned clause file.
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

# Fail unless the sidecar confirms that the named frontend route, rather than
# an inherited/manual route, produced the direct worker input.
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

# Record the exact direct-worker command and its deliberately minimal
# environment before execution.  Diagnostic lower is absent by construction.
/usr/bin/python3 - \
    "$run_root/worker-invocation.json" "$candidate_bin" "$candidate_expected_sha256" \
    "$clauses" "$clauses_sha256" "$meta" "$meta_sha256" <<'PY'
import json
from pathlib import Path
import sys

record = {
    "schema_version": 1,
    "purpose": "non-acceptance certificate-search diagnostic",
    "acceptance_evidence": False,
    "command": [sys.argv[2], "elc"],
    "binary_sha256": sys.argv[3],
    "stdin": sys.argv[4],
    "stdin_sha256": sys.argv[5],
    "frontend_meta": sys.argv[6],
    "frontend_meta_sha256": sys.argv[7],
    "environment": {
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "KM_ELC_CERT": "2",
        "KM_ELC_COVER_MODELS": "2",
        "KM_ELC_TARGET_MODELS": "32",
        "KM_ELC_TARGET_RESTARTS": "64",
        "KM_ELC_DEBUG": "1",
        "KM_ELC_DEBUG_ITEMS": "10000",
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
        KM_ELC_DEBUG_ITEMS=10000 \
        KM_ELC_TIMING=1 \
        "$candidate_bin" elc \
    < "$clauses" > "$run_root/elc.json" 2> "$run_root/elc.stderr"
elc_rc=$?
set -e
finished=$(/usr/bin/date --iso-8601=seconds)

{
    echo "job_id=$SLURM_JOB_ID"
    echo "host=$(/usr/bin/hostname)"
    echo "purpose=non-acceptance certificate-search diagnostic"
    echo "acceptance_evidence=false"
    echo "started=$started"
    echo "finished=$finished"
    echo "ofn_return_code=$ofn_rc"
    echo "elc_return_code=$elc_rc"
    echo "clauses_sha256=$clauses_sha256"
    echo "meta_sha256=$meta_sha256"
    echo "timeout_seconds=240"
    echo "slurm_cpus=$SLURM_CPUS_PER_TASK"
    echo "slurm_memory=20G"
    echo "diagnostic_lower=absent_from_env_i"
    echo "km_sha256=$candidate_expected_sha256"
    echo "source_archive_sha256=$source_archive_expected_sha256"
    echo "source_manifest_sha256=$source_manifest_expected_sha256"
    echo "build_receipt_sha256=$build_receipt_expected_sha256"
    echo "ontology_sha256=$ontology_expected_sha256"
} > "$run_root/run.meta"

/usr/bin/sha256sum \
    "$run_root/build-receipt-check.json" "$run_root/frontend.sha256" \
    "$run_root/frontend-check.json" "$run_root/worker-invocation.json" \
    "$clauses" "$meta" "$run_root/ofn.stderr" "$run_root/ofn.time" \
    "$run_root/elc.json" "$run_root/elc.stderr" "$run_root/elc.time" \
    "$run_root/run.meta" > "$run_root/outputs.sha256"

# rc=3/4 is an expected fail-closed diagnostic result; rc=124 is an expected
# bounded timeout.  Anything else indicates an execution failure, not residue.
case "$elc_rc" in
    0|3|4|124) ;;
    *) exit "$elc_rc" ;;
esac
/usr/bin/printf 'TRACE_COMPLETE non_acceptance=1 elc_rc=%s run_root=%s\n' \
    "$elc_rc" "$run_root"
