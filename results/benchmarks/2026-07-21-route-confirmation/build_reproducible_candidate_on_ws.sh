#!/bin/bash
# Freeze the current engine source and produce two byte-identical portable KM
# builds. This script deliberately refuses to run on the laptop or alongside
# another Cargo/Rust build.

set -euo pipefail

if [[ $(/usr/bin/hostname) != leechuck-office ]]; then
    echo "refusing build: run this only on leechuck-office (ws)" >&2
    exit 2
fi
if [[ $# -ne 2 ]]; then
    echo "usage: $0 SOURCE_REPOSITORY EMPTY_CAPSULE_DIRECTORY" >&2
    exit 2
fi

source_repository=$(/usr/bin/readlink -f "$1")
capsule_directory=$(/usr/bin/readlink -m "$2")
if [[ ! -f $source_repository/engine/Cargo.lock ]] \
    || [[ ! -f $source_repository/engine/Cargo.toml ]]; then
    echo "source repository lacks engine/Cargo.lock or Cargo.toml" >&2
    exit 2
fi
if [[ -e $capsule_directory ]]; then
    echo "capsule directory already exists: $capsule_directory" >&2
    exit 2
fi
if /usr/bin/pgrep -x cargo >/dev/null || /usr/bin/pgrep -x rustc >/dev/null; then
    echo "another Cargo/Rust build is running; serialize builds" >&2
    exit 3
fi

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

image_digest=sha256:646e8ceea789b00c5cfa339816a3ed44940dbf1651dc167b78f3c0aefcae0025
image_ref=rust@${image_digest}
script_directory=$(/usr/bin/readlink -f "$(/usr/bin/dirname "$0")")
receipt_writer=$script_directory/write_build_receipt.py
if [[ ! -f $receipt_writer ]]; then
    echo "missing receipt writer: $receipt_writer" >&2
    exit 2
fi

stage_directory=$(/usr/bin/mktemp -d /tmp/km-repro-build.XXXXXX)
cleanup() {
    if [[ $stage_directory == /tmp/km-repro-build.* ]] \
        && [[ -d $stage_directory ]]; then
        # Build containers run as root and therefore own target artifacts.
        # Normalize only this mktemp directory before removing it. Cleanup is
        # post-receipt and must not turn a verified build into a false failure.
        set +e
        /usr/bin/docker run --rm -v "$stage_directory:/stage" "$image_ref" \
            /bin/bash -c \
            "chown -R $(/usr/bin/id -u):$(/usr/bin/id -g) /stage" \
            >/dev/null 2>&1
        /usr/bin/rm -rf -- "$stage_directory" >/dev/null 2>&1
    fi
}
trap cleanup EXIT

/usr/bin/mkdir -p "$capsule_directory" "$stage_directory/source"
source_list=$stage_directory/source-files.list
(
    cd "$source_repository"
    /usr/bin/find engine tests -type f \
        ! -path 'engine/target/*' \
        ! -path 'engine/target-*/*' \
        ! -path 'engine/vendor/*' \
        ! -path 'engine/.cargo/*' \
        ! -path '*/__pycache__/*' \
        ! -name '*.pyc' -print0 \
        | LC_ALL=C /usr/bin/sort -z \
        | /usr/bin/tr '\0' '\n' > "$source_list"
)
if [[ ! -s $source_list ]]; then
    echo "source file list is empty" >&2
    exit 2
fi

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

/usr/bin/tar -xzf "$source_archive" -C "$stage_directory/source"
(
    cd "$stage_directory/source"
    /usr/bin/sha256sum --check --strict "$source_manifest"
) > "$capsule_directory/source-manifest-check.log"

# Pin the complete build userspace and compiler to one amd64 OCI manifest.
/usr/bin/docker pull "$image_ref" > "$capsule_directory/container-pull.log"
image_id=$(/usr/bin/docker image inspect "$image_ref" --format '{{.Id}}')
/usr/bin/docker run --rm --cpus=1 --memory=1g "$image_ref" \
    /bin/bash -c 'rustc --version --verbose' \
    > "$capsule_directory/rustc-version.txt"
/usr/bin/docker run --rm --cpus=1 --memory=1g "$image_ref" \
    /bin/bash -c 'cargo --version --verbose' \
    > "$capsule_directory/cargo-version.txt"
rustc_path=$(/usr/bin/docker run --rm --cpus=1 --memory=1g "$image_ref" \
    /bin/bash -c 'rustup which rustc')
cargo_path=$(/usr/bin/docker run --rm --cpus=1 --memory=1g "$image_ref" \
    /bin/bash -c 'rustup which cargo')
rustup_path=$(/usr/bin/docker run --rm --cpus=1 --memory=1g "$image_ref" \
    /bin/bash -c 'readlink -f "$(command -v rustup)"')
rustc_sha=$(/usr/bin/docker run --rm --cpus=1 --memory=1g "$image_ref" \
    /bin/bash -c 'sha256sum "$(rustup which rustc)"' \
    | /usr/bin/awk '{print $1}')
cargo_sha=$(/usr/bin/docker run --rm --cpus=1 --memory=1g "$image_ref" \
    /bin/bash -c 'sha256sum "$(rustup which cargo)"' \
    | /usr/bin/awk '{print $1}')
rustup_sha=$(/usr/bin/docker run --rm --cpus=1 --memory=1g "$image_ref" \
    /bin/bash -c 'sha256sum "$(readlink -f "$(command -v rustup)")"' \
    | /usr/bin/awk '{print $1}')
/usr/bin/docker run --rm --cpus=1 --memory=1g "$image_ref" \
    /bin/bash -c 'cat /etc/os-release' \
    > "$capsule_directory/container-os-release.txt"

# Resolve Cargo.lock once, then archive every dependency. The two decisive
# builds below run with both `--offline` and Docker networking disabled.
/usr/bin/mkdir -p "$stage_directory/source/engine/.cargo"
host_uid=$(/usr/bin/id -u)
host_gid=$(/usr/bin/id -g)
/usr/bin/docker run --rm --cpus=4 --memory=16g --pids-limit=1024 \
    -e HOST_UID="$host_uid" -e HOST_GID="$host_gid" \
    -v "$stage_directory/source:/src" -w /src/engine "$image_ref" \
    /bin/bash -c \
    'cargo vendor --locked --versioned-dirs vendor > .cargo/config.toml && \
     chown -R "$HOST_UID:$HOST_GID" vendor .cargo' \
    > "$capsule_directory/vendor.log" 2>&1

build_input_list=$stage_directory/build-input-files.list
(
    cd "$stage_directory/source"
    /usr/bin/find engine tests -type f -print0 \
        | LC_ALL=C /usr/bin/sort -z \
        | /usr/bin/tr '\0' '\n' > "$build_input_list"
)
build_input_manifest=$capsule_directory/build-input-files.sha256
(
    cd "$stage_directory/source"
    while IFS= read -r path; do
        /usr/bin/sha256sum -- "$path"
    done < "$build_input_list"
) > "$build_input_manifest"
build_input_archive=$capsule_directory/build-input.tar.gz
(
    cd "$stage_directory/source"
    /usr/bin/tar --create --file=- --format=gnu --sort=name --mtime='@0' \
        --owner=0 --group=0 --numeric-owner --no-recursion \
        --files-from="$build_input_list"
) | /usr/bin/gzip -n > "$build_input_archive"

/usr/bin/mkdir -p "$stage_directory/target-a" "$stage_directory/target-b"
build_one() {
    local target_directory=$1
    local log_path=$2
    /usr/bin/docker run --rm --network=none --cpus=4 --memory=16g \
        --pids-limit=1024 \
        -e CARGO_TARGET_DIR=/target \
        -e CARGO_BUILD_JOBS=4 \
        -e CARGO_INCREMENTAL=0 \
        -e SOURCE_DATE_EPOCH=0 \
        -v "$stage_directory/source:/src:ro" \
        -v "$target_directory:/target" \
        -w /src/engine "$image_ref" \
        /bin/bash -c \
        'nice -n 10 cargo build --release --locked --offline -j4 --bin km' \
        > "$log_path" 2>&1
}

build_one "$stage_directory/target-a" "$capsule_directory/build-a.log"
build_one "$stage_directory/target-b" "$capsule_directory/build-b.log"
/usr/bin/install -m 0755 "$stage_directory/target-a/release/km" \
    "$capsule_directory/km-build-a"
/usr/bin/install -m 0755 "$stage_directory/target-b/release/km" \
    "$capsule_directory/km-build-b"
/usr/bin/install -m 0755 "$0" \
    "$capsule_directory/build_reproducible_candidate_on_ws.sh"
/usr/bin/install -m 0755 "$receipt_writer" \
    "$capsule_directory/write_build_receipt.py"

/usr/bin/python3 "$receipt_writer" \
    --source-archive "$source_archive" \
    --source-manifest "$source_manifest" \
    --build-input-archive "$build_input_archive" \
    --build-input-manifest "$build_input_manifest" \
    --cargo-lock "$stage_directory/source/engine/Cargo.lock" \
    --container-image-ref "$image_ref" \
    --container-image-digest "$image_digest" \
    --container-image-id "$image_id" \
    --container-os-release "$capsule_directory/container-os-release.txt" \
    --rustc-version "$capsule_directory/rustc-version.txt" \
    --rustc-path "$rustc_path" \
    --rustc-sha256 "$rustc_sha" \
    --cargo-version "$capsule_directory/cargo-version.txt" \
    --cargo-path "$cargo_path" \
    --cargo-sha256 "$cargo_sha" \
    --rustup-path "$rustup_path" \
    --rustup-sha256 "$rustup_sha" \
    --build-a "$capsule_directory/km-build-a" \
    --build-b "$capsule_directory/km-build-b" \
    --build-a-log "$capsule_directory/build-a.log" \
    --build-b-log "$capsule_directory/build-b.log" \
    --build-script "$capsule_directory/build_reproducible_candidate_on_ws.sh" \
    --receipt-writer "$capsule_directory/write_build_receipt.py" \
    --output "$capsule_directory/build-receipt.json" \
    > "$capsule_directory/build-receipt.stdout.json"

/usr/bin/sha256sum "$capsule_directory/build-receipt.json" \
    > "$capsule_directory/build-receipt.sha256"
(
    cd "$capsule_directory"
    # Basenames keep this convenience manifest valid after the capsule is
    # relayed from ws to IBEX.  The receipt already stores the same hashes.
    /usr/bin/sha256sum km-build-a km-build-b > binaries.sha256
)
/usr/bin/cmp --silent "$capsule_directory/km-build-a" \
    "$capsule_directory/km-build-b"
echo "verified reproducible candidate: $capsule_directory/build-receipt.json"
