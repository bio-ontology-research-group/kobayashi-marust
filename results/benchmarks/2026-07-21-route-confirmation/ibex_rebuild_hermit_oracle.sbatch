#!/bin/bash
# Rebuild the tracked HermiT Oracle.java twice under one closed, hash-pinned
# JDK/classpath. This job does not classify an ontology. Its output is the
# source-bound Oracle.class capsule used by later adjudicated-route validation.
#SBATCH --job-name=km-hermit-oracle-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
export LC_ALL=C LANG=C TZ=UTC

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
driver_root=$routing_root/validation-drivers
submit_dir=${SLURM_SUBMIT_DIR:?submit from the hash-named immutable driver directory}
submit_dir_canonical=$(/usr/bin/readlink -f "$submit_dir")
driver_root_canonical=$(/usr/bin/readlink -f "$driver_root")
driver_name=$(/usr/bin/basename "$submit_dir_canonical")
driver_sha256=${driver_name#sha256-}
[[ $driver_sha256 =~ ^[0-9a-f]{64}$ ]]
/usr/bin/test "$submit_dir_canonical" = "$driver_root_canonical/$driver_name"
driver=$submit_dir_canonical/ibex_rebuild_hermit_oracle.sbatch

source=$km_root/bench/Oracle.java
source_expected_sha256=b4aec58a97cdea3a0c851b91b5342310f03484e73dbe320d037f71e4f4cd763b
retained_class=$km_root/bench/Oracle.class
retained_class_expected_sha256=60258bda6848304b1f113ba1c62c58f017d58fb848c248b45ef2792086a5d619
jdk=$km_root/bench/jdk8u492-b09
javac=$jdk/bin/javac
javac_expected_sha256=72e0a500b28f38b485a4b09849a63605893ad1bae5e15790d591f686b40b23e3
java=$jdk/bin/java
java_expected_sha256=854f27091cbf804f7fa6bfb2d958210740eb55e6d21f59d931f95a354a1a0619
classpath_root=$km_root/bench/hermit_cp
classpath_expected_count=81
classpath_expected_stream_sha256=56735fee7357b108c3e19e640f3eeada2d1e37b12cc8b5d76a02e90afb2f9919
python=/usr/bin/python3
python_expected_sha256=aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1
gnu_time=/usr/bin/time
gnu_time_expected_sha256=db73dfb29414b2a3c9ba7bb85bf10c1e32644c51f2918813398f75eaccbb45a6
run_root=$routing_root/hermit-oracle-build-${SLURM_JOB_ID}

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

for input in "$driver" "$source" "$retained_class" "$javac" "$java" \
    "$python" "$gnu_time"; do
    /usr/bin/test -s "$input"
done
/usr/bin/test "$(sha_of "$driver")" = "$driver_sha256"
/usr/bin/test "$(sha_of "$source")" = "$source_expected_sha256"
/usr/bin/test "$(sha_of "$retained_class")" = \
    "$retained_class_expected_sha256"
/usr/bin/test "$(sha_of "$javac")" = "$javac_expected_sha256"
/usr/bin/test "$(sha_of "$java")" = "$java_expected_sha256"
/usr/bin/test "$(sha_of "$python")" = "$python_expected_sha256"
/usr/bin/test "$(sha_of "$gnu_time")" = "$gnu_time_expected_sha256"

/usr/bin/mkdir -p "$run_root/build-a" "$run_root/build-b"
classpath_manifest=$run_root/hermit-classpath.sha256
/usr/bin/find "$classpath_root" -maxdepth 1 -type f -name '*.jar' -print0 \
    | /usr/bin/sort -z \
    | /usr/bin/xargs -0 /usr/bin/sha256sum \
    > "$classpath_manifest"
/usr/bin/test "$(/usr/bin/wc -l < "$classpath_manifest")" -eq \
    "$classpath_expected_count"
/usr/bin/test "$(sha_of "$classpath_manifest")" = \
    "$classpath_expected_stream_sha256"

# Hash the complete JDK payload, not just the two launchers. javac loads
# tools.jar/rt.jar and native libraries; retaining this manifest closes those
# otherwise hidden build inputs. Preserve symlink topology separately.
jdk_manifest=$run_root/jdk-files.sha256
jdk_symlinks=$run_root/jdk-symlinks.tsv
/usr/bin/find "$jdk" -type f -print0 \
    | /usr/bin/sort -z \
    | /usr/bin/xargs -0 /usr/bin/sha256sum \
    > "$jdk_manifest"
/usr/bin/find "$jdk" -type l -printf '%P\t%l\n' \
    | /usr/bin/sort > "$jdk_symlinks"
/usr/bin/test -s "$jdk_manifest"
jdk_manifest_count=$(/usr/bin/wc -l < "$jdk_manifest")
jdk_manifest_sha256=$(sha_of "$jdk_manifest")
jdk_symlink_count=$(/usr/bin/wc -l < "$jdk_symlinks")
jdk_symlinks_sha256=$(sha_of "$jdk_symlinks")

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
class_a=$run_root/build-a/Oracle.class
class_b=$run_root/build-b/Oracle.class
/usr/bin/test -s "$class_a"
/usr/bin/test -s "$class_b"
/usr/bin/cmp -s "$class_a" "$class_b"
class_sha256=$(sha_of "$class_a")
retained_byte_identical=false
if /usr/bin/cmp -s "$class_a" "$retained_class"; then
    retained_byte_identical=true
fi

/usr/bin/cp --reflink=auto "$source" "$run_root/Oracle.java"
/usr/bin/sha256sum \
    "$driver" "$run_root/Oracle.java" "$class_a" "$class_b" \
    "$retained_class" "$javac" "$java" "$python" "$gnu_time" \
    "$classpath_manifest" "$jdk_manifest" "$jdk_symlinks" \
    > "$run_root/inputs-and-outputs.sha256"

"$python" - \
    "$run_root/build-receipt.json" "$driver_sha256" "$class_sha256" \
    "$retained_byte_identical" "$run_root" <<'PY'
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


output = Path(sys.argv[1])
run_root = Path(sys.argv[5])
binary_hash = sys.argv[3]
record = {
    "schema_version": 1,
    "status": "verified_reproducible",
    "purpose": "source-bound HermiT validation oracle build",
    "acceptance_evidence": False,
    "driver_sha256": sys.argv[2],
    "source": {
        "path": str(run_root / "Oracle.java"),
        "sha256": sha256(run_root / "Oracle.java"),
    },
    "build": {
        "command": [
            "/ibex/scratch/hohndor/km/bench/jdk8u492-b09/bin/javac",
            "-cp", "/ibex/scratch/hohndor/km/bench/hermit_cp/*",
            "-d", "BUILD_DIRECTORY",
            "/ibex/scratch/hohndor/km/bench/Oracle.java",
        ],
        "environment": {
            "PATH": "/ibex/scratch/hohndor/km/bench/jdk8u492-b09/bin:/usr/bin:/bin",
            "LC_ALL": "C",
            "LANG": "C",
            "TZ": "UTC",
            "SOURCE_DATE_EPOCH": "0",
        },
        "cpus": 1,
        "memory_gib": 4,
        "twice_built_sequentially": True,
    },
    "toolchain": {
        "javac_sha256": "72e0a500b28f38b485a4b09849a63605893ad1bae5e15790d591f686b40b23e3",
        "java_sha256": "854f27091cbf804f7fa6bfb2d958210740eb55e6d21f59d931f95a354a1a0619",
        "python_sha256": "aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1",
        "gnu_time_sha256": "db73dfb29414b2a3c9ba7bb85bf10c1e32644c51f2918813398f75eaccbb45a6",
        "jdk_file_manifest": str(run_root / "jdk-files.sha256"),
        "jdk_file_manifest_sha256": sha256(run_root / "jdk-files.sha256"),
        "jdk_file_count": sum(
            1 for _ in (run_root / "jdk-files.sha256").open(encoding="utf-8")
        ),
        "jdk_symlink_manifest": str(run_root / "jdk-symlinks.tsv"),
        "jdk_symlink_manifest_sha256": sha256(run_root / "jdk-symlinks.tsv"),
        "jdk_symlink_count": sum(
            1 for _ in (run_root / "jdk-symlinks.tsv").open(encoding="utf-8")
        ),
    },
    "classpath": {
        "manifest": str(run_root / "hermit-classpath.sha256"),
        "manifest_sha256": sha256(run_root / "hermit-classpath.sha256"),
        "file_count": 81,
    },
    "outputs": {
        "build_a": str(run_root / "build-a" / "Oracle.class"),
        "build_b": str(run_root / "build-b" / "Oracle.class"),
        "build_a_sha256": sha256(run_root / "build-a" / "Oracle.class"),
        "build_b_sha256": sha256(run_root / "build-b" / "Oracle.class"),
        "binary_sha256": binary_hash,
        "byte_identical": (
            sha256(run_root / "build-a" / "Oracle.class")
            == sha256(run_root / "build-b" / "Oracle.class")
            == binary_hash
        ),
        "retained_oracle_sha256": "60258bda6848304b1f113ba1c62c58f017d58fb848c248b45ef2792086a5d619",
        "retained_byte_identical": sys.argv[4] == "true",
    },
}
if not record["outputs"]["byte_identical"]:
    record["status"] = "mismatch"
temporary = Path(str(output) + ".tmp")
temporary.write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
temporary.replace(output)
if record["status"] != "verified_reproducible":
    raise SystemExit(1)
PY

receipt_sha256=$(sha_of "$run_root/build-receipt.json")
/usr/bin/printf \
    'BUILD_COMPLETE class_sha256=%s retained_byte_identical=%s receipt_sha256=%s run_root=%s\n' \
    "$class_sha256" "$retained_byte_identical" "$receipt_sha256" "$run_root"
