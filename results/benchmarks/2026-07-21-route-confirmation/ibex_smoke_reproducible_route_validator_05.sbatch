#!/bin/bash
# Two-row smoke test for the closed route validator. Rows 0 and 93 exercise
# fresh Konclude exact-gold and source-built HermiT adjudication respectively.
# This validates the
# validator and capsule plumbing only; capsule-05 is superseded if KM source is
# edited later and this job must not be generalized into the final sweep.
#SBATCH --job-name=km-route-smoke05
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --array=0,93
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
driver_root=$routing_root/validation-drivers
submit_dir=${SLURM_SUBMIT_DIR:?submit from the immutable hash-named directory}
submit_dir_canonical=$(/usr/bin/readlink -f "$submit_dir")
driver_root_canonical=$(/usr/bin/readlink -f "$driver_root")
driver_name=$(/usr/bin/basename "$submit_dir_canonical")
driver_sha256=${driver_name#sha256-}
[[ $driver_sha256 =~ ^[0-9a-f]{64}$ ]]
/usr/bin/test "$submit_dir_canonical" = "$driver_root_canonical/$driver_name"
driver=$submit_dir_canonical/ibex_smoke_reproducible_route_validator_05.sbatch

registry=$submit_dir_canonical/ontology-solve-routes.tsv
registry_sha256=bd149a8d2a24cf46d0fd39feb12b821f2ea8cb0f00c2012f4ae4fe36e8121522
validator=$submit_dir_canonical/validate_documented_route.py
validator_sha256=53e27e3c5d1304562e859f423c4901962fc5a54ff838397b63602c92ef638fe6
runner=$submit_dir_canonical/reproducible_route_runner.py
runner_sha256=b18fd0fda258af319db2494c2be66d999a0229ad95128bff29046e51f19f3135
inner_runner=$submit_dir_canonical/validate_tail_runner.py
inner_runner_sha256=c377cc0c5844011f05d09b538efce3a951f98e82781b3d3843d19ca81edfd764
fingerprint=$submit_dir_canonical/fingerprint_tail_fulliri.py
fingerprint_sha256=b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6

capsule=$routing_root/reproducible-current-20260721-05-core
current_binary=$capsule/km-build-a
current_binary_peer=$capsule/km-build-b
current_binary_sha256=7f5e39ac7e989ca7f029090d051f009a8b2f2da5d410aeccc376d9630143c0bf
source_manifest_sha256=d5713b963d98f420939bf3843059e9edcbe06fd8c008536fee1e98202a7bf86e
build_receipt=$capsule/build-receipt.json
build_receipt_sha256=841155050f7214e88d06b64f27258a66631eeaaf4ca0f6d3949ca10bb95dca0a

konclude=$km_root/Konclude-official
konclude_sha256=5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3
konclude_library_dir=$km_root
konclude_pcre_sha256=18a3afc32488c647144f659d1629604df7ff58482a5734626dac65bd35eba8bd
konclude_runtime_count=12
konclude_runtime_stream_sha256=a65425061780e34dff5f6a460681d4599d1098906dc5b03be0ef43699406e898
ldd_sha256=2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5
python_sha256=aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1
gnu_time_sha256=db73dfb29414b2a3c9ba7bb85bf10c1e32644c51f2918813398f75eaccbb45a6
readlink_sha256=e4d766cc062ab3cef64910d951f0e5d5a10b024d706f277327d3d0a15a7032da
sha256sum_sha256=c7e38fc6c15f3fcca06ce6db0b2c726f68e9912a82b1d74ec1a02689c75074d7

hermit_build_root=$routing_root/hermit-oracle-build-49214869
hermit_java=$km_root/bench/jdk8u492-b09/bin/java
hermit_java_sha256=854f27091cbf804f7fa6bfb2d958210740eb55e6d21f59d931f95a354a1a0619
hermit_javac_sha256=72e0a500b28f38b485a4b09849a63605893ad1bae5e15790d591f686b40b23e3
hermit_oracle=$hermit_build_root/build-a/Oracle.class
hermit_oracle_sha256=60258bda6848304b1f113ba1c62c58f017d58fb848c248b45ef2792086a5d619
hermit_source=$hermit_build_root/Oracle.java
hermit_source_sha256=b4aec58a97cdea3a0c851b91b5342310f03484e73dbe320d037f71e4f4cd763b
hermit_classpath=$hermit_build_root/build-a:$km_root/bench/hermit_cp/'*'
hermit_classpath_manifest=$hermit_build_root/hermit-classpath.sha256
hermit_classpath_manifest_sha256=56735fee7357b108c3e19e640f3eeada2d1e37b12cc8b5d76a02e90afb2f9919
hermit_classpath_count=81
hermit_jdk_manifest=$hermit_build_root/jdk-files.sha256
hermit_jdk_manifest_sha256=bf22f9455ef1626151371f11269473febaa6a52846bf86c5d486c2f8bba71ea0
hermit_jdk_count=405
hermit_jdk_symlinks=$hermit_build_root/jdk-symlinks.tsv
hermit_jdk_symlinks_sha256=6e230e8f5465e17fe01eb8882411810c209456e15cd8c0c8ef495ffad81f42ff
hermit_jdk_symlink_count=2
hermit_runtime_count=5
hermit_runtime_stream_sha256=d36b6c586e5cfc0b2929266c1715d86c51d0e91c75e63b4e9df5bc1fd405c975
hermit_build_receipt=$hermit_build_root/build-receipt.json
hermit_build_receipt_sha256=46f1ac80ca8730b39e0d30604602d72400271d229dd3daa382cf6a89a70445d0
hermit_build_driver=$driver_root/sha256-b1f434da2c463b756718f0e1e801b4ff1b3ecd46bef895fc63366e82feebeb52/ibex_rebuild_hermit_oracle.sbatch
hermit_build_driver_sha256=b1f434da2c463b756718f0e1e801b4ff1b3ecd46bef895fc63366e82feebeb52

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

for pair in \
    "$driver:$driver_sha256" \
    "$registry:$registry_sha256" \
    "$validator:$validator_sha256" \
    "$runner:$runner_sha256" \
    "$inner_runner:$inner_runner_sha256" \
    "$fingerprint:$fingerprint_sha256" \
    "$current_binary:$current_binary_sha256" \
    "$current_binary_peer:$current_binary_sha256" \
    "$build_receipt:$build_receipt_sha256" \
    "$konclude:$konclude_sha256" \
    "$hermit_java:$hermit_java_sha256" \
    "$hermit_oracle:$hermit_oracle_sha256" \
    "$hermit_source:$hermit_source_sha256" \
    "$hermit_classpath_manifest:$hermit_classpath_manifest_sha256" \
    "$hermit_jdk_manifest:$hermit_jdk_manifest_sha256" \
    "$hermit_jdk_symlinks:$hermit_jdk_symlinks_sha256" \
    "$hermit_build_receipt:$hermit_build_receipt_sha256" \
    "$hermit_build_driver:$hermit_build_driver_sha256" \
    "/usr/bin/ldd:$ldd_sha256" \
    "/usr/bin/python3:$python_sha256" \
    "/usr/bin/time:$gnu_time_sha256" \
    "/usr/bin/readlink:$readlink_sha256" \
    "/usr/bin/sha256sum:$sha256sum_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    /usr/bin/test -s "$path"
    /usr/bin/test "$(sha_of "$path")" = "$expected"
done
/usr/bin/cmp -s "$current_binary" "$current_binary_peer"

run_root=$routing_root/route-validator-smoke-05-${SLURM_JOB_ID}
task_tmp=${SLURM_TMPDIR:-$run_root/tmp}
/usr/bin/mkdir -p "$run_root" "$task_tmp"

/usr/bin/env -i \
    PATH=/usr/bin:/bin LC_ALL=C PYTHONHASHSEED=0 \
    SLURM_JOB_ID="$SLURM_JOB_ID" \
    SLURM_ARRAY_JOB_ID="$SLURM_ARRAY_JOB_ID" \
    SLURM_ARRAY_TASK_ID="$SLURM_ARRAY_TASK_ID" \
    SLURM_CPUS_PER_TASK="$SLURM_CPUS_PER_TASK" \
    SLURM_TMPDIR="$task_tmp" TMPDIR="$task_tmp" \
    /usr/bin/python3 "$validator" \
        --registry "$registry" \
        --row-index "$SLURM_ARRAY_TASK_ID" \
        --km-root "$km_root" \
        --runner "$runner" \
        --fingerprint "$fingerprint" \
        --konclude "$konclude" \
        --konclude-sha256 "$konclude_sha256" \
        --konclude-library-dir "$konclude_library_dir" \
        --konclude-pcre-sha256 "$konclude_pcre_sha256" \
        --konclude-runtime-count "$konclude_runtime_count" \
        --konclude-runtime-stream-sha256 "$konclude_runtime_stream_sha256" \
        --ldd-sha256 "$ldd_sha256" \
        --hermit-java "$hermit_java" \
        --hermit-java-sha256 "$hermit_java_sha256" \
        --hermit-javac-sha256 "$hermit_javac_sha256" \
        --hermit-oracle "$hermit_oracle" \
        --hermit-oracle-sha256 "$hermit_oracle_sha256" \
        --hermit-source "$hermit_source" \
        --hermit-source-sha256 "$hermit_source_sha256" \
        --hermit-classpath "$hermit_classpath" \
        --hermit-classpath-manifest "$hermit_classpath_manifest" \
        --hermit-classpath-manifest-sha256 "$hermit_classpath_manifest_sha256" \
        --hermit-classpath-count "$hermit_classpath_count" \
        --hermit-jdk-manifest "$hermit_jdk_manifest" \
        --hermit-jdk-manifest-sha256 "$hermit_jdk_manifest_sha256" \
        --hermit-jdk-count "$hermit_jdk_count" \
        --hermit-jdk-symlinks "$hermit_jdk_symlinks" \
        --hermit-jdk-symlinks-sha256 "$hermit_jdk_symlinks_sha256" \
        --hermit-jdk-symlink-count "$hermit_jdk_symlink_count" \
        --hermit-runtime-count "$hermit_runtime_count" \
        --hermit-runtime-stream-sha256 "$hermit_runtime_stream_sha256" \
        --hermit-build-receipt "$hermit_build_receipt" \
        --hermit-build-receipt-sha256 "$hermit_build_receipt_sha256" \
        --hermit-build-driver "$hermit_build_driver" \
        --hermit-build-driver-sha256 "$hermit_build_driver_sha256" \
        --core-root "$routing_root/tail-validation-20260718/cores" \
        --result-dir "$run_root" \
        --binary-override "$current_binary" \
        --binary-override-sha256 "$current_binary_sha256" \
        --source-manifest-sha256 "$source_manifest_sha256" \
        --build-receipt "$build_receipt" \
        --build-receipt-sha256 "$build_receipt_sha256" \
        --timeout 240 \
        --memcap-mb 20480 \
        --reference-memcap-mb 20480

case "$SLURM_ARRAY_TASK_ID" in
    0) ontology=ore_ont_33.owl ;;
    93) ontology=ore_ont_2669.owl ;;
    *) echo "unsupported smoke row: $SLURM_ARRAY_TASK_ID" >&2; exit 2 ;;
esac
result=$run_root/results/$ontology.json
/usr/bin/test -s "$result"
/usr/bin/python3 - "$result" <<'PY'
import json
from pathlib import Path
import sys

record = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
print(json.dumps({
    "confirmation_status": record.get("confirmation_status"),
    "confirmed": record.get("confirmed"),
    "ontology": record.get("ontology"),
    "route": record.get("documented_route"),
    "route_specification_sha256": record.get("route_specification_sha256"),
    "reference_route_specification_sha256": record.get(
        "reference_route_specification_sha256"
    ),
}, sort_keys=True))
if record.get("confirmed") is not True:
    raise SystemExit(1)
PY
/usr/bin/sha256sum "$result"
