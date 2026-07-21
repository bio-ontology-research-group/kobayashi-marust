#!/bin/bash
# Decisive, source-reproducible ORE 10621 validation.  A route is accepted only
# when capsule-06 provenance and its compute-node runtime closure revalidate,
# the observed route is exactly ht_bridge, the source ABox maps exactly into
# the retained typed TInput, and KM's full-IRI result equals fresh Konclude.
#SBATCH --job-name=km10621-repro06
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "10621 validation failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

# IBEX injects a site LD_LIBRARY_PATH even under --export=NONE.  Re-exec this
# exact Slurm-spooled script with only the scheduler identity needed below.
clean_sentinel=__km10621_repro06_env_i_v1__
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
if [[ $# -ne 1 || $1 != "$clean_sentinel" ]]; then
    echo "invalid clean-environment sentinel" >&2
    exit 2
fi
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        SLURM_JOB_ID|SLURM_CPUS_PER_TASK|SLURM_SUBMIT_DIR|SLURM_TMPDIR|\
        PWD|SHLVL|_) ;;
        *) echo "unexpected exported variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ ${SHLVL:-} == 1 ]]
[[ $SLURM_CPUS_PER_TASK == 16 ]]
if [[ ${JAVA_TOOL_OPTIONS+x} || ${_JAVA_OPTIONS+x} \
        || ${JDK_JAVA_OPTIONS+x} || ${CLASSPATH+x} || ${JAVA_HOME+x} \
        || ${LD_LIBRARY_PATH+x} || ${LD_PRELOAD+x} || ${LD_AUDIT+x} \
        || ${PYTHONHOME+x} || ${PYTHONPATH+x} || ${PYTHONSTARTUP+x} \
        || ${PYTHONINSPECT+x} || ${PYTHONHASHSEED+x} ]]; then
    echo "ambient Java/Python/dynamic-loader overrides are forbidden" >&2
    exit 2
fi
export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0
export TZ=UTC

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
[[ $submit_dir == */routing_20260715/validation-drivers/sha256-$driver_sha256 ]]
validation_driver=$submit_dir/ibex_validate_10621_reproducible_06.sbatch

registry=$submit_dir/targeted-10621-route.tsv
registry_sha256=dcbb938e0e0383afbdc0df5f0708867651c8a8174d204c1a30005f3c16075143
validator=$submit_dir/validate_documented_route.py
validator_sha256=939459aec9ced338a1c57844d07b80761af230aea50ff87b0fdfb27a4db48ae0
runner=$submit_dir/reproducible_route_runner.py
runner_sha256=b18fd0fda258af319db2494c2be66d999a0229ad95128bff29046e51f19f3135
inner_runner=$submit_dir/validate_tail_runner.py
inner_runner_sha256=c377cc0c5844011f05d09b538efce3a951f98e82781b3d3843d19ca81edfd764
fingerprint=$submit_dir/fingerprint_tail_fulliri.py
fingerprint_sha256=b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6
tinput_auditor=$submit_dir/audit_10621_exact_tinput.py
tinput_auditor_sha256=e4d5bbb01b75be47c902c4beb3b676481143faa9afe001b8c650040745d26e63

capsule=$routing_root/reproducible-current-20260721-06-core
current_binary=$capsule/km-build-a
current_binary_peer=$capsule/km-build-b
current_binary_sha256=1dc183e7869b83c6940ab1dc0acc5ebd709fefdfea8bc307a3bf57bb4b8154a7
source_manifest_sha256=60ecac975eb3de22bc6992e061fe49daa31e188ab1f1415bc794759824d7879c
build_receipt=$capsule/build-receipt.json
build_receipt_sha256=1cf515a36b3c64bd2ea9974ddc911f450396d732006e8aafbff10fc3df832342
capsule_file_count=20
capsule_stream_sha256=4827ad3a36d9f9a3bc29b5778ae5a5cbd438842eb71c42851d1ecc68a4d7a0df
km_runtime_count=6
km_runtime_stream_sha256=ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5

konclude=$km_root/Konclude-official
konclude_sha256=5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3
konclude_library_dir=$km_root
konclude_pcre_sha256=18a3afc32488c647144f659d1629604df7ff58482a5734626dac65bd35eba8bd
konclude_runtime_count=12
konclude_runtime_stream_sha256=a65425061780e34dff5f6a460681d4599d1098906dc5b03be0ef43699406e898
ldd_sha256=2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5
python_sha256=aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1
gnu_time_sha256=db73dfb29414b2a3c9ba7bb85bf10c1e32644c51f2918813398f75eaccbb45a6

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
hermit_jdk_manifest=$hermit_build_root/jdk-files.sha256
hermit_jdk_manifest_sha256=bf22f9455ef1626151371f11269473febaa6a52846bf86c5d486c2f8bba71ea0
hermit_jdk_symlinks=$hermit_build_root/jdk-symlinks.tsv
hermit_jdk_symlinks_sha256=6e230e8f5465e17fe01eb8882411810c209456e15cd8c0c8ef495ffad81f42ff
hermit_runtime_stream_sha256=d36b6c586e5cfc0b2929266c1715d86c51d0e91c75e63b4e9df5bc1fd405c975
hermit_build_receipt=$hermit_build_root/build-receipt.json
hermit_build_receipt_sha256=46f1ac80ca8730b39e0d30604602d72400271d229dd3daa382cf6a89a70445d0
hermit_build_driver=$routing_root/validation-drivers/sha256-b1f434da2c463b756718f0e1e801b4ff1b3ecd46bef895fc63366e82feebeb52/ibex_rebuild_hermit_oracle.sbatch
hermit_build_driver_sha256=b1f434da2c463b756718f0e1e801b4ff1b3ecd46bef895fc63366e82feebeb52

ontology=$km_root/corpus/ore_ont_10621.owl
ontology_sha256=5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167
run_root=$routing_root/10621-reproducible-06-$SLURM_JOB_ID
tin=$run_root/ore_ont_10621.ht-bridge.tinput.json

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

[[ ! -e $run_root ]]
[[ $(/usr/bin/find "$submit_dir" -maxdepth 1 -type f -printf '.' | /usr/bin/wc -c) -eq 7 ]]
for pair in \
    "$validation_driver:$driver_sha256" \
    "$registry:$registry_sha256" \
    "$validator:$validator_sha256" \
    "$runner:$runner_sha256" \
    "$inner_runner:$inner_runner_sha256" \
    "$fingerprint:$fingerprint_sha256" \
    "$tinput_auditor:$tinput_auditor_sha256" \
    "$current_binary:$current_binary_sha256" \
    "$current_binary_peer:$current_binary_sha256" \
    "$build_receipt:$build_receipt_sha256" \
    "$konclude:$konclude_sha256" \
    "$konclude_library_dir/libpcre.so.3:$konclude_pcre_sha256" \
    "$hermit_java:$hermit_java_sha256" \
    "$hermit_oracle:$hermit_oracle_sha256" \
    "$hermit_source:$hermit_source_sha256" \
    "$hermit_classpath_manifest:$hermit_classpath_manifest_sha256" \
    "$hermit_jdk_manifest:$hermit_jdk_manifest_sha256" \
    "$hermit_jdk_symlinks:$hermit_jdk_symlinks_sha256" \
    "$hermit_build_receipt:$hermit_build_receipt_sha256" \
    "$hermit_build_driver:$hermit_build_driver_sha256" \
    "$ontology:$ontology_sha256" \
    "/usr/bin/ldd:$ldd_sha256" \
    "/usr/bin/python3:$python_sha256" \
    "/usr/bin/time:$gnu_time_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    /usr/bin/test -s "$path"
    [[ $(sha_of "$path") == "$expected" ]]
done
/usr/bin/cmp -s "$current_binary" "$current_binary_peer"

/usr/bin/mkdir -p "$run_root"
(
    cd "$capsule"
    /usr/bin/find . -maxdepth 1 -type f -printf '%f\0' \
        | /usr/bin/sort -z \
        | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$run_root/capsule-files.sha256"
[[ $(/usr/bin/wc -l < "$run_root/capsule-files.sha256") -eq "$capsule_file_count" ]]
[[ $(sha_of "$run_root/capsule-files.sha256") == "$capsule_stream_sha256" ]]

validator_environment=(
    PATH=/usr/bin:/bin
    LC_ALL=C
    PYTHONHASHSEED=0
    SLURM_JOB_ID="$SLURM_JOB_ID"
    SLURM_CPUS_PER_TASK="$SLURM_CPUS_PER_TASK"
)
if [[ -n ${SLURM_TMPDIR:-} ]]; then
    validator_environment+=(SLURM_TMPDIR="$SLURM_TMPDIR" TMPDIR="$SLURM_TMPDIR")
fi

set +e
/usr/bin/env -i "${validator_environment[@]}" \
    /usr/bin/python3 "$validator" \
        --registry "$registry" \
        --row-index 0 \
        --expected-registry-row-count 1 \
        --km-root "$km_root" \
        --runner "$runner" \
        --fingerprint "$fingerprint" \
        --validation-driver "$validation_driver" \
        --validation-driver-sha256 "$driver_sha256" \
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
        --hermit-classpath-count 81 \
        --hermit-jdk-manifest "$hermit_jdk_manifest" \
        --hermit-jdk-manifest-sha256 "$hermit_jdk_manifest_sha256" \
        --hermit-jdk-count 405 \
        --hermit-jdk-symlinks "$hermit_jdk_symlinks" \
        --hermit-jdk-symlinks-sha256 "$hermit_jdk_symlinks_sha256" \
        --hermit-jdk-symlink-count 2 \
        --hermit-runtime-count 5 \
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
        --km-runtime-count "$km_runtime_count" \
        --km-runtime-stream-sha256 "$km_runtime_stream_sha256" \
        --dump-tinput "$tin" \
        --timeout 240 \
        --memcap-mb 20480 \
        --reference-memcap-mb 20480
validator_rc=$?
set -e

audit_rc=2
if [[ -s $tin ]]; then
    set +e
    /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C PYTHONHASHSEED=0 \
        /usr/bin/python3 "$tinput_auditor" \
            --tin "$tin" \
            --ontology "$ontology" \
            --ontology-sha256 "$ontology_sha256" \
            --output "$run_root/tinput-audit.json"
    audit_rc=$?
    set -e
fi

/usr/bin/python3 - \
    "$run_root/results/ore_ont_10621.owl.json" \
    "$run_root/tinput-audit.json" "$run_root/ACCEPTANCE.json" \
    "$validator_rc" "$audit_rc" "$tin" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

result_path, audit_path, output_path = map(Path, sys.argv[1:4])
validator_rc, audit_rc = map(int, sys.argv[4:6])
tin_path = Path(sys.argv[6])
result = json.loads(result_path.read_text(encoding="utf-8")) if result_path.is_file() else {}
audit = json.loads(audit_path.read_text(encoding="utf-8")) if audit_path.is_file() else {}
tin_sha256 = hashlib.sha256(tin_path.read_bytes()).hexdigest() if tin_path.is_file() else ""
route = result.get("route_specification") or {}
checks = {
    "validator_exit_zero": validator_rc == 0,
    "audit_exit_zero": audit_rc == 0,
    "confirmation_status": result.get("confirmation_status") == "confirmed_exact_full_iri",
    "confirmed": result.get("confirmed") is True,
    "documented_route": result.get("documented_route") == "ht_bridge",
    "effective_route_request": result.get("effective_route_request") == "ht_bridge",
    "observed_route_trace": result.get("selected_route_trace") == "ht_bridge",
    "all_validator_checks": bool(result.get("checks"))
    and all(result["checks"].values()),
    "fresh_reference_ready": result.get("reference_ready") is True,
    "exact_binary": result.get("actual_binary_sha256")
    == "1dc183e7869b83c6940ab1dc0acc5ebd709fefdfea8bc307a3bf57bb4b8154a7",
    "exact_source_manifest": result.get("executed_source_manifest_sha256")
    == "60ecac975eb3de22bc6992e061fe49daa31e188ab1f1415bc794759824d7879c",
    "exact_runtime_closure": (result.get("km_runtime") or {}).get(
        "runtime_library_manifest_sha256"
    ) == "ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5",
    "route_semantic_environment": route.get("semantic_environment")
    == {"KM_ROUTE": "ht_bridge"},
    "route_command": route.get("command", [])[:2]
    == [
        "/ibex/scratch/hohndor/km/routing_20260715/reproducible-current-20260721-06-core/km-build-a",
        "classify",
    ],
    "tinput_record_hash": (result.get("tinput_dump") or {}).get("sha256")
    == tin_sha256 and bool(tin_sha256),
    "tinput_audit_verified": audit.get("status") == "verified_exact"
    and audit.get("supports_acceptance") is True
    and bool(audit.get("checks"))
    and all(audit["checks"].values()),
    "audit_bound_to_same_tinput": audit.get("tinput_sha256") == tin_sha256,
}
record = {
    "schema_version": 1,
    "status": "accepted" if all(checks.values()) else "rejected",
    "claim": "ORE 10621 is solved by source-built capsule-06 route ht_bridge",
    "checks": checks,
    "validator_return_code": validator_rc,
    "tinput_audit_return_code": audit_rc,
    "validation_record": str(result_path),
    "validation_record_sha256": (
        hashlib.sha256(result_path.read_bytes()).hexdigest()
        if result_path.is_file() else ""
    ),
    "tinput_audit": str(audit_path),
    "tinput_audit_sha256": (
        hashlib.sha256(audit_path.read_bytes()).hexdigest()
        if audit_path.is_file() else ""
    ),
    "tinput_sha256": tin_sha256,
}
temporary = Path(str(output_path) + ".tmp")
temporary.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
temporary.replace(output_path)
print(json.dumps(record, sort_keys=True))
if record["status"] != "accepted":
    raise SystemExit(1)
PY

/usr/bin/find "$run_root" -type f -exec /usr/bin/chmod 0444 {} +
/usr/bin/find "$run_root" -type d -exec /usr/bin/chmod 0555 {} +
/usr/bin/sha256sum "$run_root/ACCEPTANCE.json"
