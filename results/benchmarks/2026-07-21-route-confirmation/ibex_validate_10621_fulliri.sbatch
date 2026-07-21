#!/bin/bash
# Validate the exact certified-EL route for ORE 10621 with a freshly rebuilt,
# source-bound portable binary.  A successful process exit is not enough: the
# full-IRI taxonomy fingerprint must equal the retained fresh Konclude oracle.
# The required provenance variables deliberately make an opaque binary
# insufficient evidence.
#
# Certificate soundness: choice seeds, conflict bans, and target protection
# affect only whether the bounded search FINDS useful models.  Every admitted
# state is re-closed under all EL normal forms, satisfies every compiled
# residual clause, and keeps TOP non-bottom.  For every base-satisfiable named
# C, the final cover requires an admitted model with x_C alive, and the
# intersection of C's named labels across those models may contain nothing
# beyond the sound EL lower bound.  Hence every omitted named C <= D has a
# concrete full-ontology countermodel.  Any failed check or exhausted search
# declines without emitting a taxonomy.
#SBATCH --job-name=km10621-fulliri
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
export LC_ALL=C

candidate_bin=${KM_BIN:?exact freshly rebuilt portable binary}
candidate_expected_sha256=${KM_EXPECTED_SHA256:?expected SHA-256 of KM_BIN}
source_archive=${SOURCE_ARCHIVE:?exact source snapshot used by the portable build}
source_archive_expected_sha256=${SOURCE_ARCHIVE_EXPECTED_SHA256:?expected source archive SHA-256}
source_manifest=${SOURCE_MANIFEST:?per-file source manifest used by the portable build}
source_manifest_expected_sha256=${SOURCE_MANIFEST_EXPECTED_SHA256:?expected source manifest SHA-256}
build_receipt=${BUILD_PROVENANCE:?compiler/container/build-command receipt}
build_receipt_expected_sha256=${BUILD_PROVENANCE_EXPECTED_SHA256:?expected build receipt SHA-256}

validation_root=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718
oracle_root=${ORACLE_ROOT:-$validation_root/results/konclude_w16_10621}
oracle_fingerprint=${ORACLE_FINGERPRINT:-$oracle_root/fulliri.json}
oracle_fingerprint_expected_sha256=${ORACLE_FINGERPRINT_EXPECTED_SHA256:-0b70bdb6a6eb2e1dbfd22337d16b163606436501dd55f78ec6be0d92dc86da55}
oracle_run=${ORACLE_RUN:-$oracle_root/run.json}
oracle_run_expected_sha256=${ORACLE_RUN_EXPECTED_SHA256:-bb26e5c4bace42769be54be361fd5b5ba07faaaa214ffc95c5010bfc98e893f6}
oracle_taxonomy=${ORACLE_TAXONOMY:-$oracle_root/taxonomy.owl}
oracle_taxonomy_expected_sha256=${ORACLE_TAXONOMY_EXPECTED_SHA256:-d50eeeef9029c705ac8219f4b7f86c21f9b6b07ef17f16c92c5128fa55a283cd}

fingerprinter=${FINGERPRINTER:-$validation_root/fingerprint_tail_fulliri.py}
fingerprinter_expected_sha256=${FINGERPRINTER_EXPECTED_SHA256:-b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6}
ontology=${ONTOLOGY:-/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl}
ontology_expected_sha256=${ONTOLOGY_EXPECTED_SHA256:-5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167}
run_root=${RUN_ROOT:-/ibex/scratch/hohndor/km/routing_20260715/10621-fulliri-${SLURM_JOB_ID}}

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

/usr/bin/test -x "$candidate_bin"
/usr/bin/test -s "$source_archive"
/usr/bin/test -s "$source_manifest"
/usr/bin/test -s "$build_receipt"
/usr/bin/test -s "$oracle_fingerprint"
/usr/bin/test -s "$oracle_run"
/usr/bin/test -s "$oracle_taxonomy"
/usr/bin/test -s "$fingerprinter"
/usr/bin/test -s "$ontology"

/usr/bin/test "$(sha_of "$candidate_bin")" = "$candidate_expected_sha256"
/usr/bin/test "$(sha_of "$source_archive")" = "$source_archive_expected_sha256"
/usr/bin/test "$(sha_of "$source_manifest")" = "$source_manifest_expected_sha256"
/usr/bin/test "$(sha_of "$build_receipt")" = "$build_receipt_expected_sha256"
/usr/bin/test "$(sha_of "$oracle_fingerprint")" = "$oracle_fingerprint_expected_sha256"
/usr/bin/test "$(sha_of "$oracle_run")" = "$oracle_run_expected_sha256"
/usr/bin/test "$(sha_of "$oracle_taxonomy")" = "$oracle_taxonomy_expected_sha256"
/usr/bin/test "$(sha_of "$fingerprinter")" = "$fingerprinter_expected_sha256"
/usr/bin/test "$(sha_of "$ontology")" = "$ontology_expected_sha256"

/usr/bin/mkdir -p "$run_root"
/usr/bin/sha256sum \
    "$candidate_bin" "$source_archive" "$source_manifest" "$build_receipt" \
    "$ontology" "$fingerprinter" "$oracle_fingerprint" "$oracle_run" \
    "$oracle_taxonomy" > "$run_root/inputs.sha256"

# A receipt hash alone only identifies a document.  Check that the document
# actually binds this candidate and these source artifacts to two byte-equal,
# locked, offline, network-isolated builds with pinned toolchain identities.
/usr/bin/python3 - \
    "$build_receipt" "$candidate_expected_sha256" \
    "$source_archive_expected_sha256" "$source_manifest_expected_sha256" \
    "$run_root/build-receipt-check.json" <<'PY'
import json
from pathlib import Path
import re
import sys

receipt_path = Path(sys.argv[1])
candidate_sha = sys.argv[2]
source_archive_sha = sys.argv[3]
source_manifest_sha = sys.argv[4]
output_path = Path(sys.argv[5])
receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
build = receipt.get("build", {})
outputs = receipt.get("outputs", {})
source = receipt.get("source", {})
container = receipt.get("container", {})
toolchain = receipt.get("toolchain", {})
rustc_verbose = toolchain.get("rustc_version_verbose", "")
rustc_match = re.search(r"(?m)^commit-hash:\s*([0-9a-f]{40})$", rustc_verbose)
rustc_commit = toolchain.get("rustc_commit") or (
    rustc_match.group(1) if rustc_match else None
)
container_digest = container.get("image_digest")
tool_hashes = {
    toolchain.get("rustc_sha256"),
    toolchain.get("cargo_sha256"),
    toolchain.get("rustup_sha256"),
}

checks = {
    "status_verified_reproducible": receipt.get("status")
    == "verified_reproducible",
    "byte_identical": outputs.get("byte_identical") is True,
    "binary_hash": outputs.get("binary_sha256") == candidate_sha,
    "build_a_hash": outputs.get("build_a_sha256") == candidate_sha,
    "build_b_hash": outputs.get("build_b_sha256") == candidate_sha,
    "source_archive_hash": source.get("archive_sha256") == source_archive_sha,
    "source_manifest_hash": source.get("manifest_sha256") == source_manifest_sha,
    "cargo_locked": build.get("cargo_locked") is True,
    "offline_vendored": build.get("offline_vendored") is True,
    "network_disabled": build.get("network_disabled") is True,
    "container_digest_present": isinstance(container_digest, str)
    and container_digest.startswith("sha256:")
    and len(container_digest) == 71,
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
    "source_archive_sha256": source_archive_sha,
    "source_manifest_sha256": source_manifest_sha,
    "container_digest": container_digest,
    "rustc_commit": rustc_commit,
}
tmp = Path(str(output_path) + ".tmp")
tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
tmp.replace(output_path)
print(json.dumps(record, sort_keys=True))
if record["status"] != "ok":
    raise SystemExit(1)
PY

# Verify that the retained fingerprint is still bound to the retained fresh
# Konclude run and its primary OWL/XML output before treating it as an oracle.
/usr/bin/python3 - \
    "$oracle_fingerprint" "$oracle_run" "$oracle_taxonomy_expected_sha256" \
    "$ontology_expected_sha256" > "$run_root/oracle-check.json" <<'PY'
import json
import sys

fingerprint = json.load(open(sys.argv[1], encoding="utf-8"))
run = json.load(open(sys.argv[2], encoding="utf-8"))
taxonomy_sha = sys.argv[3]
ontology_sha = sys.argv[4]

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
record = {"status": "ok" if all(checks.values()) else "mismatch", "checks": checks}
print(json.dumps(record, indent=2, sort_keys=True))
if record["status"] != "ok":
    raise SystemExit(1)
PY

# Named routes normalize their own routing variables.  Remove every inherited
# KM switch first, then add only measurement controls.  In particular,
# KM_ELC_DIAGNOSTIC_LOWER stays absent: exit 0 from elc_cert therefore requires
# the full, fail-closed completeness certificate to pass.
while IFS='=' read -r name _; do
    if [[ "$name" == KM_* ]]; then
        unset "$name"
    fi
done < <(/usr/bin/env)
export KM_TIMING=1
export KM_ELC_COVER_MODELS=2
export KM_ELC_TARGET_MODELS=32
export KM_ELC_TARGET_RESTARTS=64
/usr/bin/test -z "${KM_ELC_DIAGNOSTIC_LOWER:-}"

started=$(/usr/bin/date --iso-8601=seconds)
set +e
/usr/bin/time -v -o "$run_root/km.time" \
    /usr/bin/timeout -k 10 240 \
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
    echo "started=$started"
    echo "finished=$finished"
    echo "km_return_code=$km_rc"
    echo "command=$candidate_bin classify --route elc_cert $ontology"
    echo "route=elc_cert"
    echo "route_bundle=KM_THREADS=16,KM_PAR_MEM_GB=18,KM_HT_MEM_GB=18,KM_KEEP_CHAIN_AXIOMS=1,KM_MECHANISM=elc,KM_NO_HT_RULES=1,KM_NO_HT_RACE=1,KM_NO_ABSORB_PORTFOLIO=1,KM_ABSORB=0,KM_ELC_FORCE=1,KM_ELC_CERT=2"
    echo "search_controls=KM_ELC_COVER_MODELS=2,KM_ELC_TARGET_MODELS=32,KM_ELC_TARGET_RESTARTS=64"
    echo "instrumentation=KM_TIMING=1"
    echo "diagnostic_lower=unset"
    echo "certificate_soundness=search-only choices; admitted states reclose EL, satisfy all residuals, keep TOP nonbottom, and witness an empty extra-label intersection for every base-alive named subject"
    echo "slurm_cpus=$SLURM_CPUS_PER_TASK"
    echo "slurm_memory=20G"
    echo "timeout_seconds=240"
    echo "maximum_resident_kib=$km_peak_kib"
    echo "km_sha256=$candidate_expected_sha256"
    echo "source_archive_sha256=$source_archive_expected_sha256"
    echo "source_manifest_sha256=$source_manifest_expected_sha256"
    echo "build_receipt_sha256=$build_receipt_expected_sha256"
    echo "ontology_sha256=$ontology_expected_sha256"
    echo "fingerprinter_sha256=$fingerprinter_expected_sha256"
    echo "oracle_fingerprint_sha256=$oracle_fingerprint_expected_sha256"
    echo "oracle_run_sha256=$oracle_run_expected_sha256"
    echo "oracle_taxonomy_sha256=$oracle_taxonomy_expected_sha256"
} > "$run_root/run.meta"

/usr/bin/test "$km_rc" -eq 0
/usr/bin/test -s "$run_root/km.json"
/usr/bin/grep -q 'KM_TIMING frontend done.* route=elc_cert' "$run_root/km.stderr"

/usr/bin/time -v -o "$run_root/fingerprint.time" \
    /usr/bin/python3 "$fingerprinter" \
    --input "$run_root/km.json" \
    --format json \
    --source-ontology "$ontology" \
    --output-prefix "$run_root/km-fulliri" \
    > "$run_root/fingerprint.stdout" 2> "$run_root/fingerprint.stderr"

/usr/bin/python3 - \
    "$run_root/km-fulliri.json" "$oracle_fingerprint" "$run_root/comparison.json" <<'PY'
import json
from pathlib import Path
import sys

candidate_path = Path(sys.argv[1])
oracle_path = Path(sys.argv[2])
output_path = Path(sys.argv[3])
candidate = json.loads(candidate_path.read_text(encoding="utf-8"))
oracle = json.loads(oracle_path.read_text(encoding="utf-8"))
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
    "status": "match" if not differences else "mismatch",
    "checked_fields": fields,
    "differences": differences,
    "candidate": {field: candidate.get(field) for field in fields},
    "konclude": {field: oracle.get(field) for field in fields},
}
tmp = Path(str(output_path) + ".tmp")
tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
tmp.replace(output_path)
print(json.dumps(record, sort_keys=True))
if differences:
    raise SystemExit(1)
PY

/usr/bin/sha256sum \
    "$run_root/km.json" "$run_root/km.stderr" "$run_root/km-fulliri.json" \
    "$run_root/km-fulliri.nodes.tsv.gz" "$run_root/km-fulliri.unsat.txt.gz" \
    "$run_root/comparison.json" "$run_root/build-receipt-check.json" \
    > "$run_root/outputs.sha256"
/usr/bin/cat "$run_root/comparison.json"
