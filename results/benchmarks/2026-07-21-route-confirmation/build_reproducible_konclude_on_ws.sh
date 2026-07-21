#!/bin/bash
# Build the exact official Konclude v0.7.0-1138 source twice on ws and retain
# enough source, toolchain, Qt, and runtime evidence to replay the build.

set -euo pipefail

expected_host=leechuck-office
expected_commit=0002e80635403960a7df5d93bd0e8f994d4952d0
expected_tag=v0.7.0-1138
source_date_epoch=1624053538

if [[ $(/usr/bin/hostname) != "$expected_host" ]]; then
    echo "refusing build: run this only on $expected_host (ws)" >&2
    exit 2
fi
if [[ $# -ne 2 ]]; then
    echo "usage: $0 CLEAN_KONCLUDE_SOURCE EMPTY_CAPSULE_DIRECTORY" >&2
    exit 2
fi

source_repository=$(/usr/bin/readlink -f "$1")
capsule_directory=$(/usr/bin/readlink -m "$2")
if [[ ! -f $source_repository/KoncludeWithoutRedland.pro ]] \
        || [[ ! -f $source_repository/revision-git.h ]]; then
    echo "source directory is not a Konclude source checkout" >&2
    exit 2
fi
if [[ -e $capsule_directory ]]; then
    echo "capsule directory already exists: $capsule_directory" >&2
    exit 2
fi

actual_commit=$(/usr/bin/git -C "$source_repository" rev-parse HEAD)
actual_tag=$(/usr/bin/git -C "$source_repository" describe --tags --exact-match)
if [[ $actual_commit != "$expected_commit" || $actual_tag != "$expected_tag" ]]; then
    echo "unexpected Konclude revision: $actual_commit $actual_tag" >&2
    exit 2
fi
if [[ -n $(/usr/bin/git -C "$source_repository" status --porcelain=v1 --untracked-files=all) ]]; then
    echo "Konclude source checkout is not clean" >&2
    exit 2
fi

for process_name in cargo rustc qmake make g++ cc1plus; do
    if /usr/bin/pgrep -x "$process_name" >/dev/null; then
        echo "another build process is running: $process_name" >&2
        exit 3
    fi
done
read -r load_one _ </proc/loadavg
available_kib=$(/usr/bin/awk '/^MemAvailable:/ {print $2}' /proc/meminfo)
if /usr/bin/awk -v load="$load_one" 'BEGIN {exit !(load > 8.0)}'; then
    echo "load $load_one exceeds the conservative ws build limit" >&2
    exit 3
fi
if [[ ${available_kib:-0} -lt 33554432 ]]; then
    echo "less than 32 GiB available; refusing build" >&2
    exit 3
fi

for required in git qmake make g++ python3 tar gzip sha256sum find sort; do
    command -v "$required" >/dev/null
done

/usr/bin/mkdir -p "$capsule_directory"
stage_directory=$(/usr/bin/mktemp -d /tmp/konclude-repro-build.XXXXXX)
cleanup() {
    if [[ $stage_directory == /tmp/konclude-repro-build.* ]] \
            && [[ -d $stage_directory ]]; then
        /usr/bin/find "$stage_directory" -depth -delete >/dev/null 2>&1 || true
    fi
}
trap cleanup EXIT

source_list=$stage_directory/source-files.list
(
    cd "$source_repository"
    /usr/bin/find . -path './.git' -prune -o -type f -printf '%P\0' \
        | LC_ALL=C /usr/bin/sort -z \
        | /usr/bin/tr '\0' '\n' > "$source_list"
)
[[ -s $source_list ]]

source_manifest=$capsule_directory/source-files.sha256
(
    cd "$source_repository"
    while IFS= read -r path; do
        /usr/bin/sha256sum -- "$path"
    done < "$source_list"
) > "$source_manifest"

source_archive=$capsule_directory/source.tar.gz
(
    cd "$source_repository"
    /usr/bin/tar --create --file=- --format=gnu --sort=name --mtime='@0' \
        --owner=0 --group=0 --numeric-owner --no-recursion \
        --files-from="$source_list"
) | /usr/bin/gzip -n > "$source_archive"

/usr/bin/mkdir -p "$stage_directory/source-a" "$stage_directory/source-b"
/usr/bin/tar -xzf "$source_archive" -C "$stage_directory/source-a"
/usr/bin/tar -xzf "$source_archive" -C "$stage_directory/source-b"
(
    cd "$stage_directory/source-a"
    /usr/bin/sha256sum --check --strict "$source_manifest"
) > "$capsule_directory/source-manifest-check-a.log"
(
    cd "$stage_directory/source-b"
    /usr/bin/sha256sum --check --strict "$source_manifest"
) > "$capsule_directory/source-manifest-check-b.log"

{
    /usr/bin/printf 'field\tvalue\n'
    /usr/bin/printf 'repository\thttps://github.com/konclude/Konclude.git\n'
    /usr/bin/printf 'commit\t%s\n' "$actual_commit"
    /usr/bin/printf 'tag\t%s\n' "$actual_tag"
    /usr/bin/printf 'source_date_epoch\t%s\n' "$source_date_epoch"
    /usr/bin/printf 'source_file_count\t%s\n' "$(/usr/bin/wc -l < "$source_manifest")"
} > "$capsule_directory/source-revision.tsv"
/usr/bin/cp /etc/os-release "$capsule_directory/host-os-release.txt"
/usr/bin/uname -a > "$capsule_directory/uname.txt"
/usr/bin/dpkg-query -W -f='${binary:Package}\t${Version}\n' \
    | LC_ALL=C /usr/bin/sort > "$capsule_directory/dpkg-packages.tsv"
/usr/bin/sha256sum /var/lib/dpkg/status \
    > "$capsule_directory/dpkg-status.sha256"

qmake_path=$(/usr/bin/readlink -f "$(command -v qmake)")
make_path=$(/usr/bin/readlink -f "$(command -v make)")
gxx_path=$(/usr/bin/readlink -f "$(command -v g++)")
ld_path=$(/usr/bin/readlink -f "$(command -v ld)")
as_path=$(/usr/bin/readlink -f "$(command -v as)")
moc_path=$(/usr/bin/readlink -f "$(command -v moc)")
cc1plus_path=$(/usr/bin/readlink -f "$(g++ -print-prog-name=cc1plus)")

qmake -v > "$capsule_directory/qmake-version.txt" 2>&1
qmake -query > "$capsule_directory/qmake-query.txt"
g++ --version > "$capsule_directory/gxx-version.txt"
make --version > "$capsule_directory/make-version.txt"
ld --version > "$capsule_directory/ld-version.txt"
g++ -v -E -x c++ /dev/null \
    > "$capsule_directory/gxx-search-paths.stdout" \
    2> "$capsule_directory/gxx-search-paths.stderr"

{
    /usr/bin/printf 'logical_name\tresolved_path\tsha256\n'
    for pair in \
        "qmake:$qmake_path" "make:$make_path" "g++:$gxx_path" \
        "cc1plus:$cc1plus_path" "ld:$ld_path" "as:$as_path" \
        "moc:$moc_path"; do
        logical_name=${pair%%:*}
        resolved_path=${pair#*:}
        /usr/bin/test -f "$resolved_path"
        /usr/bin/printf '%s\t%s\t%s\n' \
            "$logical_name" "$resolved_path" \
            "$(/usr/bin/sha256sum "$resolved_path" | /usr/bin/awk '{print $1}')"
    done
} > "$capsule_directory/toolchain-files.tsv"

qt_headers=$(qmake -query QT_INSTALL_HEADERS)
[[ -d $qt_headers ]]
(
    cd "$qt_headers"
    /usr/bin/find . -type f -printf '%P\0' | LC_ALL=C /usr/bin/sort -z \
        | while IFS= read -r -d '' path; do
            /usr/bin/sha256sum -- "$path"
        done
) > "$capsule_directory/qt-headers.sha256"

build_one() {
    local source_tree=$1
    local build_log=$2
    (
        cd "$source_tree"
        export LC_ALL=C
        export LANG=C
        export TZ=UTC
        export SOURCE_DATE_EPOCH="$source_date_epoch"
        qmake -o Makefile KoncludeWithoutRedland.pro \
            "QMAKE_CXXFLAGS_RELEASE+=-ffile-prefix-map=$source_tree=." \
            "QMAKE_CXXFLAGS_RELEASE+=-fmacro-prefix-map=$source_tree=." \
            'QMAKE_LFLAGS+=-Wl,--build-id=sha1'
        nice -n 10 make -j4
    ) > "$build_log" 2>&1
}

build_one "$stage_directory/source-a" "$capsule_directory/build-a.log"
build_one "$stage_directory/source-b" "$capsule_directory/build-b.log"
/usr/bin/install -m 0755 "$stage_directory/source-a/Release/Konclude" \
    "$capsule_directory/Konclude-build-a"
/usr/bin/install -m 0755 "$stage_directory/source-b/Release/Konclude" \
    "$capsule_directory/Konclude-build-b"
/usr/bin/install -m 0755 "$0" \
    "$capsule_directory/build_reproducible_konclude_on_ws.sh"

/usr/bin/cmp --silent "$capsule_directory/Konclude-build-a" \
    "$capsule_directory/Konclude-build-b"
/usr/bin/file "$capsule_directory/Konclude-build-a" \
    > "$capsule_directory/binary-file.txt"
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/ldd "$capsule_directory/Konclude-build-a" \
    > "$capsule_directory/ldd.stdout" 2> "$capsule_directory/ldd.stderr"
if /usr/bin/grep -q 'not found' "$capsule_directory/ldd.stdout"; then
    echo "Konclude has unresolved runtime libraries" >&2
    exit 4
fi
/usr/bin/awk '
    $2 == "=>" && substr($3, 1, 1) == "/" { print $3; next }
    substr($1, 1, 1) == "/" { print $1 }
' "$capsule_directory/ldd.stdout" | LC_ALL=C /usr/bin/sort -u \
    > "$stage_directory/runtime-paths.txt"
while IFS= read -r runtime_path; do
    /usr/bin/sha256sum "$runtime_path"
done < "$stage_directory/runtime-paths.txt" \
    > "$capsule_directory/runtime-files.sha256"

/usr/bin/python3 -I - \
    "$capsule_directory" "$actual_commit" "$actual_tag" \
    "$source_date_epoch" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

root = Path(sys.argv[1])
commit, tag, epoch = sys.argv[2:]

def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()

files = {}
for path in sorted(root.iterdir(), key=lambda item: item.name):
    if path.is_file() and path.name != "build-receipt.json":
        files[path.name] = digest(path)

binary_a = root / "Konclude-build-a"
binary_b = root / "Konclude-build-b"
binary_sha = digest(binary_a)
receipt = {
    "schema_version": 1,
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
        "qmake_command": [
            "qmake", "-o", "Makefile", "KoncludeWithoutRedland.pro",
            "QMAKE_CXXFLAGS_RELEASE+=-ffile-prefix-map=SOURCE_TREE=.",
            "QMAKE_CXXFLAGS_RELEASE+=-fmacro-prefix-map=SOURCE_TREE=.",
            "QMAKE_LFLAGS+=-Wl,--build-id=sha1",
        ],
        "make_command": ["nice", "-n", "10", "make", "-j4"],
        "jobs": 4,
        "sequential_fresh_trees": True,
        "network_used": False,
    },
    "outputs": {
        "build_a": binary_a.name,
        "build_b": binary_b.name,
        "build_a_sha256": binary_sha,
        "build_b_sha256": digest(binary_b),
        "byte_identical": binary_a.read_bytes() == binary_b.read_bytes(),
    },
    "artifacts": files,
}
if not receipt["outputs"]["byte_identical"]:
    raise SystemExit("Konclude builds are not byte-identical")
(root / "build-receipt.json").write_text(
    json.dumps(receipt, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
PY

/usr/bin/sha256sum "$capsule_directory/build-receipt.json" \
    > "$capsule_directory/build-receipt.sha256"
(
    cd "$capsule_directory"
    /usr/bin/sha256sum Konclude-build-a Konclude-build-b > binaries.sha256
)
echo "verified reproducible Konclude candidate: $capsule_directory/build-receipt.json"
