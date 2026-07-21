#!/bin/bash
# Build the exact official Konclude v0.7.0-1138 source twice on one IBEX
# compute node, then package the exact non-system runtime libraries.
#SBATCH --job-name=kon-src-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:55:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "Konclude source build failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__konclude_source_build_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    optional_slurm=()
    if [[ -n ${SLURM_TMPDIR:-} ]]; then
        optional_slurm+=(SLURM_TMPDIR="$SLURM_TMPDIR")
    fi
    exec /usr/bin/env -i \
        OUTPUT_ROOT="${OUTPUT_ROOT:?export a new persistent OUTPUT_ROOT}" \
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
[[ $SLURM_CPUS_PER_TASK == 4 ]]
[[ -n $SLURM_JOB_ID ]]

export PATH=/usr/bin:/bin
export LC_ALL=C
export LANG=C
export TZ=UTC
export SOURCE_DATE_EPOCH=1624053538
export PYTHONHASHSEED=0

# Environment Modules is initialized explicitly after env -i. The module file
# itself and every resolved compiler/Qt input are captured below.
source /etc/profile.d/modules.sh
module purge
module use /sw/rl9c/modulefiles/compilers
module load qt/5.15.5/gnu-12.2.0
# The site GCC module exports LD_RUN_PATH, which silently writes the compiler
# installation into DT_RPATH even when qmake's Qt RPATH is disabled. Linking
# still finds GCC and Qt through LIBRARY_PATH; runtime discovery is packaged
# separately below.
unset LD_RUN_PATH
[[ ! ${LD_RUN_PATH+x} ]]

routing_root=/ibex/scratch/hohndor/km/routing_20260715
source_root=$routing_root/konclude-source-v0.7.0-1138
source_archive=$source_root/source.tar.gz
source_manifest=$source_root/source-files.sha256
source_archive_sha256=936b65796da3209eed83d90264614067bd7d8f03133d089a64dd8bea9618076f
source_manifest_sha256=a188a16ac440259e58c289ea766cd457a402e7c85ceb6c3e5b11a7ca08b116d2
source_file_count=5525
expected_commit=0002e80635403960a7df5d93bd0e8f994d4952d0
expected_tag=v0.7.0-1138

driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
[[ $submit_dir == */routing_20260715/validation-drivers/sha256-$driver_sha256 ]]
submit_copy=$submit_dir/ibex_build_reproducible_konclude.sbatch
[[ -f $submit_copy && ! -L $submit_copy ]]
[[ $(/usr/bin/sha256sum "$submit_copy" | /usr/bin/awk '{print $1}') == "$driver_sha256" ]]

[[ $OUTPUT_ROOT == $routing_root/konclude-oracle-builds/* ]]
[[ ! -e $OUTPUT_ROOT ]]
[[ -f $source_archive && ! -L $source_archive ]]
[[ -f $source_manifest && ! -L $source_manifest ]]
[[ $(/usr/bin/sha256sum "$source_archive" | /usr/bin/awk '{print $1}') == "$source_archive_sha256" ]]
[[ $(/usr/bin/sha256sum "$source_manifest" | /usr/bin/awk '{print $1}') == "$source_manifest_sha256" ]]
[[ $(/usr/bin/wc -l < "$source_manifest") -eq $source_file_count ]]

stage_base=${SLURM_TMPDIR:-/tmp}
stage=$(/usr/bin/mktemp -d "$stage_base/konclude-source-build.XXXXXX")
cleanup() {
    if [[ $stage == "$stage_base"/konclude-source-build.* ]] \
            && [[ -d $stage ]]; then
        /usr/bin/find "$stage" -depth -delete >/dev/null 2>&1 || true
    fi
}
trap cleanup EXIT

/usr/bin/mkdir -p "$OUTPUT_ROOT" "$stage/source-a" "$stage/source-b"
/usr/bin/tar -xzf "$source_archive" -C "$stage/source-a"
/usr/bin/tar -xzf "$source_archive" -C "$stage/source-b"
(
    cd "$stage/source-a"
    /usr/bin/sha256sum --check --strict "$source_manifest"
) > "$OUTPUT_ROOT/source-manifest-check-a.log"
(
    cd "$stage/source-b"
    /usr/bin/sha256sum --check --strict "$source_manifest"
) > "$OUTPUT_ROOT/source-manifest-check-b.log"
/usr/bin/cp "$source_archive" "$OUTPUT_ROOT/source.tar.gz"
/usr/bin/cp "$source_manifest" "$OUTPUT_ROOT/source-files.sha256"
/usr/bin/install -m 0755 "$submit_copy" \
    "$OUTPUT_ROOT/ibex_build_reproducible_konclude.sbatch"

module -t list > "$OUTPUT_ROOT/modules.txt" 2>&1
/usr/bin/env | LC_ALL=C /usr/bin/sort > "$OUTPUT_ROOT/build-environment.txt"
/usr/bin/cp /etc/os-release "$OUTPUT_ROOT/compute-os-release.txt"
/usr/bin/uname -a > "$OUTPUT_ROOT/uname.txt"

qmake_path=$(/usr/bin/readlink -f "$(command -v qmake)")
make_path=$(/usr/bin/readlink -f "$(command -v make)")
gxx_path=$(/usr/bin/readlink -f "$(command -v g++)")
ld_path=$(/usr/bin/readlink -f "$(command -v ld)")
as_path=$(/usr/bin/readlink -f "$(command -v as)")
moc_path=$(/usr/bin/readlink -f "$(command -v moc)")
readelf_path=$(/usr/bin/readlink -f "$(command -v readelf)")
cc1plus_path=$(/usr/bin/readlink -f "$(g++ -print-prog-name=cc1plus)")
qmake -v > "$OUTPUT_ROOT/qmake-version.txt" 2>&1
qmake -query > "$OUTPUT_ROOT/qmake-query.txt"
g++ --version > "$OUTPUT_ROOT/gxx-version.txt"
make --version > "$OUTPUT_ROOT/make-version.txt"
ld --version > "$OUTPUT_ROOT/ld-version.txt"
readelf --version > "$OUTPUT_ROOT/readelf-version.txt"
{
    /usr/bin/printf 'logical_name\tresolved_path\tsha256\n'
    for pair in \
        "qmake:$qmake_path" "make:$make_path" "g++:$gxx_path" \
        "cc1plus:$cc1plus_path" "ld:$ld_path" "as:$as_path" \
        "moc:$moc_path" "readelf:$readelf_path"; do
        logical_name=${pair%%:*}
        resolved_path=${pair#*:}
        [[ -f $resolved_path ]]
        /usr/bin/printf '%s\t%s\t%s\n' \
            "$logical_name" "$resolved_path" \
            "$(/usr/bin/sha256sum "$resolved_path" | /usr/bin/awk '{print $1}')"
    done
} > "$OUTPUT_ROOT/toolchain-files.tsv"

qt_headers=$(qmake -query QT_INSTALL_HEADERS)
[[ -d $qt_headers ]]
(
    cd "$qt_headers"
    /usr/bin/find . -type f -printf '%P\0' | LC_ALL=C /usr/bin/sort -z \
        | while IFS= read -r -d '' path; do
            /usr/bin/sha256sum -- "$path"
        done
) > "$OUTPUT_ROOT/qt-headers.sha256"

build_one() {
    local source_tree=$1
    local build_log=$2
    (
        cd "$source_tree"
        qmake -o Makefile KoncludeWithoutRedland.pro \
            'CONFIG+=no_qt_rpath' \
            "QMAKE_CXXFLAGS_RELEASE+=-ffile-prefix-map=$source_tree=." \
            "QMAKE_CXXFLAGS_RELEASE+=-fmacro-prefix-map=$source_tree=." \
            'QMAKE_LFLAGS+=-Wl,--build-id=sha1'
        /usr/bin/nice -n 10 /usr/bin/make -j4
    ) > "$build_log" 2>&1
}

build_one "$stage/source-a" "$OUTPUT_ROOT/build-a.log"
build_one "$stage/source-b" "$OUTPUT_ROOT/build-b.log"
/usr/bin/install -m 0755 "$stage/source-a/Release/Konclude" \
    "$OUTPUT_ROOT/Konclude-build-a"
/usr/bin/install -m 0755 "$stage/source-b/Release/Konclude" \
    "$OUTPUT_ROOT/Konclude-build-b"
/usr/bin/cmp -s "$OUTPUT_ROOT/Konclude-build-a" \
    "$OUTPUT_ROOT/Konclude-build-b"
/usr/bin/file "$OUTPUT_ROOT/Konclude-build-a" \
    > "$OUTPUT_ROOT/binary-file.txt"
/usr/bin/readelf -d "$OUTPUT_ROOT/Konclude-build-a" \
    > "$OUTPUT_ROOT/binary-dynamic.txt"
if /usr/bin/grep -Eq '\((RPATH|RUNPATH)\)' \
        "$OUTPUT_ROOT/binary-dynamic.txt"; then
    echo "source build retained a build-host runtime path" >&2
    exit 4
fi

# First resolve with the loaded module stack, then package every /sw library
# under its SONAME basename. The final runtime check uses only this directory
# plus compute-node system libraries.
/usr/bin/ldd "$OUTPUT_ROOT/Konclude-build-a" \
    > "$OUTPUT_ROOT/ldd-module.stdout" \
    2> "$OUTPUT_ROOT/ldd-module.stderr"
if /usr/bin/grep -q 'not found' "$OUTPUT_ROOT/ldd-module.stdout"; then
    echo "module runtime has unresolved libraries" >&2
    exit 4
fi
/usr/bin/mkdir "$OUTPUT_ROOT/runtime-lib"
/usr/bin/awk '
    $2 == "=>" && substr($3, 1, 1) == "/" { print $3; next }
    substr($1, 1, 1) == "/" { print $1 }
' "$OUTPUT_ROOT/ldd-module.stdout" | LC_ALL=C /usr/bin/sort -u \
    > "$stage/module-runtime-paths.txt"
while IFS= read -r runtime_path; do
    if [[ $runtime_path == /sw/* ]]; then
        destination=$OUTPUT_ROOT/runtime-lib/$(/usr/bin/basename "$runtime_path")
        [[ ! -e $destination ]]
        /usr/bin/cp -L "$runtime_path" "$destination"
    fi
done < "$stage/module-runtime-paths.txt"

closed_environment=(
    PATH=/usr/bin:/bin
    LC_ALL=C
    PYTHONHASHSEED=0
    LD_LIBRARY_PATH="$OUTPUT_ROOT/runtime-lib"
)
/usr/bin/env -i "${closed_environment[@]}" \
    /usr/bin/ldd "$OUTPUT_ROOT/Konclude-build-a" \
    > "$OUTPUT_ROOT/ldd.stdout" 2> "$OUTPUT_ROOT/ldd.stderr"
if /usr/bin/grep -q 'not found' "$OUTPUT_ROOT/ldd.stdout"; then
    echo "packaged runtime has unresolved libraries" >&2
    exit 4
fi
if /usr/bin/grep -q '/sw/' "$OUTPUT_ROOT/ldd.stdout"; then
    echo "packaged runtime still resolves a library from /sw" >&2
    exit 4
fi
/usr/bin/awk '
    $2 == "=>" && substr($3, 1, 1) == "/" { print $3; next }
    substr($1, 1, 1) == "/" { print $1 }
' "$OUTPUT_ROOT/ldd.stdout" | LC_ALL=C /usr/bin/sort -u \
    > "$OUTPUT_ROOT/runtime-paths.txt"
while IFS= read -r runtime_path; do
    [[ -f $runtime_path ]]
    /usr/bin/sha256sum "$runtime_path"
done < "$OUTPUT_ROOT/runtime-paths.txt" \
    > "$OUTPUT_ROOT/runtime-files.sha256"

{
    /usr/bin/printf 'field\tvalue\n'
    /usr/bin/printf 'repository\thttps://github.com/konclude/Konclude.git\n'
    /usr/bin/printf 'commit\t%s\n' "$expected_commit"
    /usr/bin/printf 'tag\t%s\n' "$expected_tag"
    /usr/bin/printf 'source_date_epoch\t%s\n' "$SOURCE_DATE_EPOCH"
    /usr/bin/printf 'source_file_count\t%s\n' "$source_file_count"
    /usr/bin/printf 'slurm_job_id\t%s\n' "$SLURM_JOB_ID"
    /usr/bin/printf 'host\t%s\n' "$(/usr/bin/hostname)"
    /usr/bin/printf 'driver_sha256\t%s\n' "$driver_sha256"
} > "$OUTPUT_ROOT/source-revision.tsv"

/usr/bin/python3 -I - \
    "$OUTPUT_ROOT" "$expected_commit" "$expected_tag" \
    "$SOURCE_DATE_EPOCH" "$driver_sha256" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

root = Path(sys.argv[1])
commit, tag, epoch, driver_sha = sys.argv[2:]

def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()

files = {}
for path in sorted(root.rglob("*"), key=lambda item: str(item.relative_to(root))):
    if path.is_file() and path.name != "build-receipt.json":
        files[str(path.relative_to(root))] = digest(path)

binary_a = root / "Konclude-build-a"
binary_b = root / "Konclude-build-b"
binary_sha = digest(binary_a)
receipt = {
    "schema_version": 2,
    "status": "verified_reproducible",
    "source": {
        "repository": "https://github.com/konclude/Konclude.git",
        "commit": commit,
        "tag": tag,
        "source_date_epoch": int(epoch),
        "archive_sha256": digest(root / "source.tar.gz"),
        "manifest_sha256": digest(root / "source-files.sha256"),
        "manifest_file_count": sum(
            1 for _ in (root / "source-files.sha256").open(encoding="utf-8")
        ),
    },
    "build": {
        "project": "KoncludeWithoutRedland.pro",
        "module": "qt/5.15.5/gnu-12.2.0",
        "qmake_command": [
            "qmake", "-o", "Makefile", "KoncludeWithoutRedland.pro",
            "CONFIG+=no_qt_rpath",
            "QMAKE_CXXFLAGS_RELEASE+=-ffile-prefix-map=SOURCE_TREE=.",
            "QMAKE_CXXFLAGS_RELEASE+=-fmacro-prefix-map=SOURCE_TREE=.",
            "QMAKE_LFLAGS+=-Wl,--build-id=sha1",
        ],
        "make_command": ["nice", "-n", "10", "make", "-j4"],
        "jobs": 4,
        "sequential_fresh_trees": True,
        "network_used": False,
        "ld_run_path_cleared": True,
        "slurm_job_id": int(__import__("os").environ["SLURM_JOB_ID"]),
    },
    "outputs": {
        "build_a": binary_a.name,
        "build_b": binary_b.name,
        "build_a_sha256": binary_sha,
        "build_b_sha256": digest(binary_b),
        "byte_identical": binary_a.read_bytes() == binary_b.read_bytes(),
    },
    "runtime": {
        "library_directory": str(root / "runtime-lib"),
        "manifest_sha256": digest(root / "runtime-files.sha256"),
        "manifest_file_count": sum(
            1 for _ in (root / "runtime-files.sha256").open(encoding="utf-8")
        ),
    },
    "driver_sha256": driver_sha,
    "artifacts": files,
}
if not receipt["outputs"]["byte_identical"]:
    raise SystemExit("Konclude builds are not byte-identical")
(root / "build-receipt.json").write_text(
    json.dumps(receipt, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
PY

/usr/bin/sha256sum "$OUTPUT_ROOT/build-receipt.json" \
    > "$OUTPUT_ROOT/build-receipt.sha256"
(
    cd "$OUTPUT_ROOT"
    /usr/bin/sha256sum Konclude-build-a Konclude-build-b > binaries.sha256
)

# Freeze the complete capsule after every check and receipt has succeeded.
/usr/bin/find "$OUTPUT_ROOT" -type f -exec /usr/bin/chmod a-w {} +
/usr/bin/find "$OUTPUT_ROOT" -type d -exec /usr/bin/chmod a-w {} +
echo "verified reproducible Konclude candidate: $OUTPUT_ROOT/build-receipt.json"
