#!/bin/bash
# Non-acceptance diagnostic: replay only the Flagellum subject through the
# exact capsule-09 production route and expose KPSet candidate disposition.
#SBATCH --job-name=km10621-flag-kpset
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "Flagellum KPSet diagnostic failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km10621_flagellum_kpset_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    optional_slurm=()
    if [[ -n ${SLURM_TMPDIR:-} ]]; then
        optional_slurm+=(SLURM_TMPDIR="$SLURM_TMPDIR")
    fi
    exec /usr/bin/env -i \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_CPUS_PER_TASK="${SLURM_CPUS_PER_TASK:?missing Slurm CPU count}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        "${optional_slurm[@]}" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        SLURM_JOB_ID|SLURM_CPUS_PER_TASK|SLURM_SUBMIT_DIR|SLURM_TMPDIR|PWD|SHLVL|_) ;;
        *) echo "unexpected exported variable: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ ${SHLVL:-} == 1 ]]
[[ $SLURM_CPUS_PER_TASK == 16 ]]
export PATH=/usr/bin:/bin LC_ALL=C LANG=C TZ=UTC

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
validation_root=$routing_root/validation-drivers
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
validation_root=$(/usr/bin/readlink -f "$validation_root")
driver_name=$(/usr/bin/basename "$submit_dir")
driver_sha256=${driver_name#sha256-}
[[ $driver_sha256 =~ ^[0-9a-f]{64}$ ]]
[[ $submit_dir == "$validation_root/$driver_name" ]]
driver=$submit_dir/ibex_diagnose_10621_flagellum_kpset.sbatch

capsule=$routing_root/reproducible-current-20260721-09-core
binary=$capsule/km-build-a
binary_peer=$capsule/km-build-b
binary_sha256=41975f2ed894ba22cc9ec898a554bfe9c3521533bc1cd3bd9627c297c05d87dd
source_manifest_sha256=3d2fb63c74f6ab93c63c2e993320814546fbc0b9466cac1214b7baeb5f9596ba
build_receipt=$capsule/build-receipt.json
build_receipt_sha256=3254df1de9adf313a1fb7794b75a196fcc356bc9095e3bea886a8f541dc817b2
capsule_file_count=20
capsule_stream_sha256=f543af277da7765e569e30f6bf058bf0fb2b9da766260de2e356f1cbaa307fad
runtime_capture=$routing_root/runtime-closures/capsule09-capture-20260721-01
runtime_file_count=6
runtime_manifest_sha256=ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5
runtime_capture_count=7
runtime_capture_stream_sha256=f03da51126a3ca20e53f0f5ceb8eca3d93cfbe99a917ddbe607dbc7e8271c185
ontology=$km_root/corpus/ore_ont_10621.owl
ontology_sha256=5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167
flagellum_index=6171
run_root=$routing_root/diagnostics/10621-flagellum-kpset-${SLURM_JOB_ID}
python=/usr/bin/python3.9
python_sha256=aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1
gnu_time=/usr/bin/time
gnu_time_sha256=db73dfb29414b2a3c9ba7bb85bf10c1e32644c51f2918813398f75eaccbb45a6

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

[[ ! -e $run_root ]]
[[ $(/usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -type f -printf '.' | /usr/bin/wc -c) -eq 1 ]]
for pair in \
    "$driver:$driver_sha256" \
    "$binary:$binary_sha256" \
    "$binary_peer:$binary_sha256" \
    "$build_receipt:$build_receipt_sha256" \
    "$runtime_capture/runtime-files.sha256:$runtime_manifest_sha256" \
    "$ontology:$ontology_sha256" \
    "$python:$python_sha256" \
    "$gnu_time:$gnu_time_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    [[ -f $path && ! -L $path ]]
    [[ $(sha_of "$path") == "$expected" ]]
done
/usr/bin/cmp -s "$binary" "$binary_peer"

/usr/bin/mkdir -p "$run_root"
(
    cd "$capsule"
    /usr/bin/find . -mindepth 1 -maxdepth 1 -type f -printf '%f\0' \
        | /usr/bin/sort -z \
        | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$run_root/capsule-files.sha256"
[[ $(/usr/bin/wc -l < "$run_root/capsule-files.sha256") -eq $capsule_file_count ]]
[[ $(sha_of "$run_root/capsule-files.sha256") == "$capsule_stream_sha256" ]]

(
    cd "$runtime_capture"
    /usr/bin/find . -mindepth 1 -maxdepth 1 -type f -printf '%f\0' \
        | /usr/bin/sort -z \
        | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$run_root/runtime-capture-files.sha256"
[[ $(/usr/bin/wc -l < "$run_root/runtime-capture-files.sha256") -eq $runtime_capture_count ]]
[[ $(sha_of "$run_root/runtime-capture-files.sha256") == "$runtime_capture_stream_sha256" ]]
[[ $(/usr/bin/wc -l < "$runtime_capture/runtime-files.sha256") -eq $runtime_file_count ]]
/usr/bin/sha256sum -c --quiet "$runtime_capture/runtime-files.sha256"

"$python" -I - "$build_receipt" "$source_manifest_sha256" "$binary_sha256" <<'PY'
import json
from pathlib import Path
import sys

receipt = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
if receipt.get("status") != "verified_reproducible":
    raise SystemExit("unverified build receipt")
if receipt.get("source", {}).get("manifest_sha256") != sys.argv[2]:
    raise SystemExit("source manifest mismatch")
outputs = receipt.get("outputs", {})
if not outputs.get("byte_identical"):
    raise SystemExit("builds were not byte-identical")
if {
    outputs.get("binary_sha256"),
    outputs.get("build_a_sha256"),
    outputs.get("build_b_sha256"),
} != {sys.argv[3]}:
    raise SystemExit("binary receipt mismatch")
PY

set +e
"$gnu_time" -v -o "$run_root/route.time" \
    /usr/bin/timeout -k 15 240 \
    /usr/bin/env -i \
        PATH=/usr/bin:/bin LC_ALL=C LANG=C TZ=UTC \
        KM_ROUTE=ht_bridge \
        KM_BRIDGE_ONLY_SUBJECT="$flagellum_index" \
        KM_BRIDGE_PROGRESS=1 \
        KM_TIMING=1 \
        "$binary" classify "$ontology" \
    > "$run_root/route.stdout" 2> "$run_root/route.stderr"
route_rc=$?
set -e
/usr/bin/printf '%s\n' "$route_rc" > "$run_root/route.exit-code"

route_trace_count=$(/usr/bin/grep -c '^KM_ROUTE_SELECTED=ht_bridge$' "$run_root/route.stderr" || true)
organ_part_lines=$(/usr/bin/grep -c 'Flagellum v Organ_part' "$run_root/route.stderr" || true)

"$python" -I - "$run_root" "$driver_sha256" "$binary_sha256" \
    "$source_manifest_sha256" "$ontology_sha256" "$route_rc" \
    "$route_trace_count" "$organ_part_lines" <<'PY'
import hashlib
import json
import os
from pathlib import Path
import sys


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


root = Path(sys.argv[1])
record = {
    "schema_version": 1,
    "status": "completed" if int(sys.argv[6]) == 0 else "failed",
    "acceptance_evidence": False,
    "purpose": "replay the 10621 Flagellum KPSet disposition",
    "job_id": int(os.environ["SLURM_JOB_ID"]),
    "driver_sha256": sys.argv[2],
    "binary_sha256": sys.argv[3],
    "source_manifest_sha256": sys.argv[4],
    "ontology_sha256": sys.argv[5],
    "command": [
        "/usr/bin/timeout", "-k", "15", "240",
        "/usr/bin/env", "-i",
        "PATH=/usr/bin:/bin", "LC_ALL=C", "LANG=C", "TZ=UTC",
        "KM_ROUTE=ht_bridge", "KM_BRIDGE_ONLY_SUBJECT=6171",
        "KM_BRIDGE_PROGRESS=1", "KM_TIMING=1",
        "/ibex/scratch/hohndor/km/routing_20260715/reproducible-current-20260721-09-core/km-build-a",
        "classify", "/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl",
    ],
    "route_exit_code": int(sys.argv[6]),
    "route_trace_count": int(sys.argv[7]),
    "flagellum_organ_part_diagnostic_line_count": int(sys.argv[8]),
    "stdout_sha256": sha256(root / "route.stdout"),
    "stderr_sha256": sha256(root / "route.stderr"),
    "time_sha256": sha256(root / "route.time"),
}
(root / "RECEIPT.json").write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
PY

/usr/bin/sha256sum "$driver" "$binary" "$binary_peer" "$build_receipt" \
    "$ontology" "$run_root"/* > "$run_root/inputs-and-outputs.sha256"
/usr/bin/chmod -R a-w "$run_root"
/usr/bin/printf 'DONE run_root=%s route_rc=%s trace_count=%s organ_part_lines=%s\n' \
    "$run_root" "$route_rc" "$route_trace_count" "$organ_part_lines"
[[ $route_rc -eq 0 ]]
[[ $route_trace_count -eq 1 ]]
