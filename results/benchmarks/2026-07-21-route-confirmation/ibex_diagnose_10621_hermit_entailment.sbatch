#!/bin/bash
# Build the tracked one-edge HermiT oracle twice, then adjudicate the only
# fresh Konclude/KM disagreement for ORE 10621 on the exact corpus bytes.
#SBATCH --job-name=km10621-hermit-edge
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:40:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "HermiT edge diagnostic failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR
export LC_ALL=C LANG=C TZ=UTC

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
driver_root=$routing_root/validation-drivers
submit_dir=${SLURM_SUBMIT_DIR:?submit from a hash-named immutable driver directory}
submit_dir=$(/usr/bin/readlink -f "$submit_dir")
driver_root=$(/usr/bin/readlink -f "$driver_root")
driver_name=$(/usr/bin/basename "$submit_dir")
driver_sha256=${driver_name#sha256-}
[[ $driver_sha256 =~ ^[0-9a-f]{64}$ ]]
[[ $submit_dir == "$driver_root/$driver_name" ]]

driver=$submit_dir/ibex_diagnose_10621_hermit_entailment.sbatch
source=$submit_dir/HermitNamedEntailmentOracle.java
source_sha256=24a70db8aeb573cc7aa935a6837909aa60bc1f1558938d4a267e94906e5f2993
ontology=$km_root/corpus/ore_ont_10621.owl
ontology_sha256=5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167
sub=http://nlm.nih.gov/ontology/FMAInOWL#Flagellum
super=http://nlm.nih.gov/ontology/FMAInOWL#Organ_part

hermit_build_root=$routing_root/hermit-oracle-build-49214869
jdk=$km_root/bench/jdk8u492-b09
java=$jdk/bin/java
javac=$jdk/bin/javac
java_sha256=854f27091cbf804f7fa6bfb2d958210740eb55e6d21f59d931f95a354a1a0619
javac_sha256=72e0a500b28f38b485a4b09849a63605893ad1bae5e15790d591f686b40b23e3
classpath_root=$km_root/bench/hermit_cp
classpath_manifest=$hermit_build_root/hermit-classpath.sha256
classpath_manifest_sha256=56735fee7357b108c3e19e640f3eeada2d1e37b12cc8b5d76a02e90afb2f9919
classpath_count=81
jdk_manifest=$hermit_build_root/jdk-files.sha256
jdk_manifest_sha256=bf22f9455ef1626151371f11269473febaa6a52846bf86c5d486c2f8bba71ea0
jdk_count=405
jdk_symlinks=$hermit_build_root/jdk-symlinks.tsv
jdk_symlinks_sha256=6e230e8f5465e17fe01eb8882411810c209456e15cd8c0c8ef495ffad81f42ff
jdk_symlink_count=2
python=/usr/bin/python3.9
python_sha256=aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1
gnu_time=/usr/bin/time
gnu_time_sha256=db73dfb29414b2a3c9ba7bb85bf10c1e32644c51f2918813398f75eaccbb45a6
run_root=$routing_root/diagnostics/10621-hermit-edge-${SLURM_JOB_ID}

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

[[ ! -e $run_root ]]
/usr/bin/mkdir -p "$run_root/build-a" "$run_root/build-b"

expected_submit_entries=(
    HermitNamedEntailmentOracle.java
    ibex_diagnose_10621_hermit_entailment.sbatch
)
mapfile -t actual_submit_entries < <(
    /usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -printf '%f\n' \
        | /usr/bin/sort
)
[[ ${#actual_submit_entries[@]} -eq ${#expected_submit_entries[@]} ]]
for index in "${!expected_submit_entries[@]}"; do
    [[ ${actual_submit_entries[$index]} == "${expected_submit_entries[$index]}" ]]
done

for pair in \
    "$driver:$driver_sha256" \
    "$source:$source_sha256" \
    "$ontology:$ontology_sha256" \
    "$java:$java_sha256" \
    "$javac:$javac_sha256" \
    "$classpath_manifest:$classpath_manifest_sha256" \
    "$jdk_manifest:$jdk_manifest_sha256" \
    "$jdk_symlinks:$jdk_symlinks_sha256" \
    "$python:$python_sha256" \
    "$gnu_time:$gnu_time_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    [[ -f $path && ! -L $path ]]
    [[ $(sha_of "$path") == "$expected" ]]
done
[[ $(/usr/bin/wc -l < "$classpath_manifest") -eq $classpath_count ]]
[[ $(/usr/bin/wc -l < "$jdk_manifest") -eq $jdk_count ]]
[[ $(/usr/bin/wc -l < "$jdk_symlinks") -eq $jdk_symlink_count ]]

# Verify every jar and JDK file against the previously frozen manifests.
/usr/bin/sha256sum -c --quiet "$classpath_manifest"
/usr/bin/sha256sum -c --quiet "$jdk_manifest"

build_one() {
    label=$1
    destination=$2
    "$gnu_time" -v -o "$run_root/$label.time" \
        /usr/bin/env -i \
            PATH="$jdk/bin:/usr/bin:/bin" \
            LC_ALL=C LANG=C TZ=UTC SOURCE_DATE_EPOCH=0 \
            "$javac" -cp "$classpath_root/*" -d "$destination" "$source" \
        > "$run_root/$label.stdout" 2> "$run_root/$label.stderr"
}

build_one build-a "$run_root/build-a"
build_one build-b "$run_root/build-b"
class_a=$run_root/build-a/HermitNamedEntailmentOracle.class
class_b=$run_root/build-b/HermitNamedEntailmentOracle.class
[[ -s $class_a && -s $class_b ]]
/usr/bin/cmp -s "$class_a" "$class_b"
class_sha256=$(sha_of "$class_a")

set +e
"$gnu_time" -v -o "$run_root/oracle.time" \
    /usr/bin/env -i \
        PATH="$jdk/bin:/usr/bin:/bin" \
        LC_ALL=C LANG=C TZ=UTC \
        /usr/bin/timeout -k 15 1800 \
        "$java" -Xmx28g -cp "$run_root/build-a:$classpath_root/*" \
        HermitNamedEntailmentOracle "$ontology" "$sub" "$super" \
    > "$run_root/oracle.json" 2> "$run_root/oracle.stderr"
oracle_rc=$?
set -e
/usr/bin/printf '%s\n' "$oracle_rc" > "$run_root/oracle.exit-code"

if [[ $oracle_rc -eq 0 ]]; then
    "$python" -I - "$run_root/oracle.json" <<'PY'
import json
from pathlib import Path
import sys

record = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
required = {
    "ontology",
    "sub",
    "super",
    "consistent",
    "sub_satisfiable",
    "subclass_entailed",
    "counterexample_satisfiable",
}
if set(record) != required:
    raise SystemExit("unexpected oracle JSON schema")
if record["ontology"] != "ore_ont_10621.owl":
    raise SystemExit("wrong ontology in oracle output")
if record["sub"] != "http://nlm.nih.gov/ontology/FMAInOWL#Flagellum":
    raise SystemExit("wrong subclass in oracle output")
if record["super"] != "http://nlm.nih.gov/ontology/FMAInOWL#Organ_part":
    raise SystemExit("wrong superclass in oracle output")
if not record["consistent"] or not record["sub_satisfiable"]:
    raise SystemExit("unexpected consistency or satisfiability result")
if record["subclass_entailed"] == record["counterexample_satisfiable"]:
    raise SystemExit("entailment and counterexample answers are not complements")
PY
fi

/usr/bin/sha256sum \
    "$driver" "$source" "$ontology" "$java" "$javac" \
    "$classpath_manifest" "$jdk_manifest" "$jdk_symlinks" \
    "$class_a" "$class_b" "$run_root/oracle.json" \
    "$run_root/oracle.stderr" "$run_root/oracle.exit-code" \
    > "$run_root/inputs-and-outputs.sha256"

"$python" -I - "$run_root" "$driver_sha256" "$class_sha256" \
    "$source_sha256" "$ontology_sha256" "$oracle_rc" <<'PY'
import hashlib
import json
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
    "purpose": "independent adjudication of the 10621 Flagellum edge",
    "job_id": int(__import__("os").environ["SLURM_JOB_ID"]),
    "driver_sha256": sys.argv[2],
    "source_sha256": sys.argv[4],
    "ontology_sha256": sys.argv[5],
    "oracle_exit_code": int(sys.argv[6]),
    "build": {
        "command": [
            "/ibex/scratch/hohndor/km/bench/jdk8u492-b09/bin/javac",
            "-cp",
            "/ibex/scratch/hohndor/km/bench/hermit_cp/*",
            "-d",
            "BUILD_DIRECTORY",
            "HermitNamedEntailmentOracle.java",
        ],
        "environment": {
            "PATH": "/ibex/scratch/hohndor/km/bench/jdk8u492-b09/bin:/usr/bin:/bin",
            "LC_ALL": "C",
            "LANG": "C",
            "TZ": "UTC",
            "SOURCE_DATE_EPOCH": "0",
        },
        "twice_built_sequentially": True,
        "build_a_sha256": sha256(root / "build-a" / "HermitNamedEntailmentOracle.class"),
        "build_b_sha256": sha256(root / "build-b" / "HermitNamedEntailmentOracle.class"),
        "byte_identical": (
            sha256(root / "build-a" / "HermitNamedEntailmentOracle.class")
            == sha256(root / "build-b" / "HermitNamedEntailmentOracle.class")
            == sys.argv[3]
        ),
    },
    "run": {
        "command": [
            "/ibex/scratch/hohndor/km/bench/jdk8u492-b09/bin/java",
            "-Xmx28g",
            "-cp",
            "BUILD_A:/ibex/scratch/hohndor/km/bench/hermit_cp/*",
            "HermitNamedEntailmentOracle",
            "/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl",
            "http://nlm.nih.gov/ontology/FMAInOWL#Flagellum",
            "http://nlm.nih.gov/ontology/FMAInOWL#Organ_part",
        ],
        "environment": {
            "PATH": "/ibex/scratch/hohndor/km/bench/jdk8u492-b09/bin:/usr/bin:/bin",
            "LC_ALL": "C",
            "LANG": "C",
            "TZ": "UTC",
        },
        "timeout_seconds": 1800,
        "memory_gib": 32,
        "cpus": 1,
        "stdout_sha256": sha256(root / "oracle.json"),
        "stderr_sha256": sha256(root / "oracle.stderr"),
    },
}
(root / "RECEIPT.json").write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
if record["status"] != "completed" or not record["build"]["byte_identical"]:
    raise SystemExit(1)
PY

/usr/bin/chmod -R a-w "$run_root"
/usr/bin/printf 'DONE run_root=%s class_sha256=%s oracle_rc=%s\n' \
    "$run_root" "$class_sha256" "$oracle_rc"
[[ $oracle_rc -eq 0 ]]
