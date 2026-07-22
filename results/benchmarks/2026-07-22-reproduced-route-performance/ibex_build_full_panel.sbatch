#!/bin/bash
# Build every source-pinned executable used by the all-options ORE panel.
# Builds are sequential and use one shared Cargo target cache.
#SBATCH --job-name=km-panel-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=08:00:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260722/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "panel build failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export LC_ALL=C
export CARGO_NET_GIT_FETCH_WITH_CLI=true
export CARGO_TERM_COLOR=never
export RUST_BACKTRACE=1

root=/ibex/scratch/hohndor/km/full-panel-20260722
build_root=$root/build
tmp_root=${SLURM_TMPDIR:-$root/tmp}/km-panel-build-$SLURM_JOB_ID
script_dir=$(/usr/bin/readlink -f "${SLURM_SUBMIT_DIR:?missing Slurm submit directory}")
benchmark_root=/ibex/scratch/hohndor/km/bench
km_commit=8c731f43b3c8a277f5fd7a25687e35afb4c4045e
rustdl_commit=8c2bb1bf43d936e56d77ae439c04d2feb3f6ebf5
sequoia_commit=c5248ec7be302efc850cf07ab30a0ea651db81b6
sbt_sha256=4a61ffe26046609923c8db6fa4b8931d936b1326142c5c89256dccd5e886d147
jdk=/ibex/scratch/hohndor/km/bench/jdk8u492-b09

/usr/bin/mkdir -p "$build_root/bin" "$build_root/receipts" "$build_root/patches" "$tmp_root"

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

record_binary() {
    local key=$1 binary=$2 revision=$3 variant=$4
    local destination=$build_root/bin/km-$key
    /usr/bin/install -m 0555 "$binary" "$destination"
    /usr/bin/python3 - "$key" "$destination" "$revision" "$variant" "$SLURM_JOB_ID" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

key, binary, revision, variant, job = sys.argv[1:]
path = Path(binary)
digest = hashlib.sha256(path.read_bytes()).hexdigest()
receipt = {
    "schema_version": 1,
    "key": key,
    "binary": str(path),
    "binary_sha256": digest,
    "source_revision": revision,
    "variant": variant,
    "slurm_job_id": job,
}
out = path.parents[1] / "receipts" / f"km-{key}.json"
out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
PY
}

/usr/bin/git clone --quiet https://github.com/bio-ontology-research-group/kobayashi-marust.git "$tmp_root/km"
/usr/bin/git -C "$tmp_root/km" checkout --quiet --detach "$km_commit"
[[ $(/usr/bin/git -C "$tmp_root/km" rev-parse HEAD) == "$km_commit" ]]
export CARGO_TARGET_DIR=$tmp_root/cargo-target-km

build_km_tree() {
    local source=$1 key=$2 revision=$3 variant=$4
    (
        cd "$source/engine"
        /usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs "$SLURM_CPUS_PER_TASK"
    )
    record_binary "$key" "$CARGO_TARGET_DIR/release/km" "$revision" "$variant"
}

build_km_tree "$tmp_root/km" main "$km_commit" current-main

stage_revisions=(
    17c0c7581278d4b355efa04e9444e03b87cba9ab
    757c073f3a8a29ffdeb1403f9bbf4f0fe43326f9
    536ca58b32bf20ae2d24426dae74f6d1b399d2fc
    0883fe5b65ce8743ea711f76e77ec434ff4b1865
    3fd3b77e52700b530b3f1ade11b945ffb9afdbfb
    794f6c21282b38f9e2e28523c66496e7fa7c84a1
    3d1926a9f987ed0939c3282047b753e97afa8b44
    a639ab59bfb20b04f0131a2b7b7cb727117a936b
    55222f1704cb48341e91e2571dd039646074fbd4
    61b35c0f82ed07b29d9c117d492a03154866af69
    8407ce2caa17ffcf64d46aed308ede6903de1c80
)
for revision in "${stage_revisions[@]}"; do
    key=stage-${revision:0:12}
    source=$tmp_root/$key
    /usr/bin/git -C "$tmp_root/km" worktree add --quiet --detach "$source" "$revision"
    build_km_tree "$source" "$key" "$revision" chronological-optimization-stage
done

ablation_revisions=(
    757c073f3a8a29ffdeb1403f9bbf4f0fe43326f9
    3d1926a9f987ed0939c3282047b753e97afa8b44
    55222f1704cb48341e91e2571dd039646074fbd4
    61b35c0f82ed07b29d9c117d492a03154866af69
    8407ce2caa17ffcf64d46aed308ede6903de1c80
)
for revision in "${ablation_revisions[@]}"; do
    key=ablate-${revision:0:12}
    source=$tmp_root/$key
    /usr/bin/git -C "$tmp_root/km" worktree add --quiet --detach "$source" "$km_commit"
    /usr/bin/git -C "$source" revert --no-commit "$revision"
    /usr/bin/git -C "$source" diff --cached --check
    /usr/bin/git -C "$source" diff --cached --binary > "$build_root/patches/$key.patch"
    [[ -s $build_root/patches/$key.patch ]]
    build_km_tree "$source" "$key" "$km_commit" "current-main-minus-$revision"
done
(
    cd "$build_root/patches"
    /usr/bin/sha256sum ablate-*.patch > "$build_root/ablation-patches.sha256"
)

/usr/bin/git clone --quiet https://github.com/MaastrichtU-IDS/rustdl.git "$tmp_root/rustdl"
/usr/bin/git -C "$tmp_root/rustdl" checkout --quiet --detach "$rustdl_commit"
[[ $(/usr/bin/git -C "$tmp_root/rustdl" rev-parse HEAD) == "$rustdl_commit" ]]
export CARGO_TARGET_DIR=$tmp_root/cargo-target-rustdl
(
    cd "$tmp_root/rustdl"
    /usr/bin/nice -n 5 cargo build --release --locked -p owl-dl-cli --jobs "$SLURM_CPUS_PER_TASK"
)
/usr/bin/install -m 0555 "$CARGO_TARGET_DIR/release/rustdl" "$build_root/bin/rustdl"

"$jdk/bin/javac" -cp "$benchmark_root/hermit_cp/*" -d "$build_root/bin" \
    "$script_dir/FullIriHermitOracle.java"

/usr/bin/git clone --quiet https://github.com/andrewdbate/Sequoia.git "$tmp_root/sequoia"
/usr/bin/git -C "$tmp_root/sequoia" checkout --quiet --detach "$sequoia_commit"
[[ $(/usr/bin/git -C "$tmp_root/sequoia" rev-parse HEAD) == "$sequoia_commit" ]]
/usr/bin/curl -fsSL --retry 5 -o "$tmp_root/sbt-launch-1.3.8.jar" \
    https://repo.maven.apache.org/maven2/org/scala-sbt/sbt-launch/1.3.8/sbt-launch-1.3.8.jar
[[ $(sha_of "$tmp_root/sbt-launch-1.3.8.jar") == "$sbt_sha256" ]]
export JAVA_HOME=$jdk
export PATH=$JAVA_HOME/bin:/home/hohndor/.cargo/bin:/usr/bin:/bin
export SBT_OPTS='-Xms1g -Xmx24g -XX:+UseG1GC'
(
    cd "$tmp_root/sequoia"
    "$JAVA_HOME/bin/java" -Xms1g -Xmx24g -jar "$tmp_root/sbt-launch-1.3.8.jar" \
        'project cli' 'universal:packageBin'
)
sequoia_zip=$(/usr/bin/find "$tmp_root/sequoia/reasoner-cli/target/universal" \
    -maxdepth 1 -type f -name 'sequoia-command-line-interface-*.zip' -print -quit)
[[ -s $sequoia_zip ]]
/usr/bin/mkdir -p "$build_root/sequoia"
(
    cd "$build_root/sequoia"
    /usr/bin/unzip -q "$sequoia_zip"
)
sequoia_bin=$(/usr/bin/find "$build_root/sequoia" -type f -path '*/bin/sequoia' -print -quit)
[[ -s $sequoia_bin ]]
/usr/bin/chmod 0555 "$sequoia_bin"
/usr/bin/ln -sfn "$sequoia_bin" "$build_root/bin/sequoia"
(
    cd "$build_root/sequoia"
    /usr/bin/find . -type f -print0 | /usr/bin/sort -z \
        | /usr/bin/xargs -0 /usr/bin/sha256sum > "$build_root/sequoia-files.sha256"
)

/usr/bin/python3 - "$build_root" "$km_commit" "$rustdl_commit" "$sequoia_commit" \
    "$SLURM_JOB_ID" "$script_dir/ibex_build_full_panel.sbatch" "$sbt_sha256" <<'PY'
import hashlib
import json
from pathlib import Path
import subprocess
import sys

root, km_revision, rustdl_revision, sequoia_revision, job, build_script, sbt_sha = sys.argv[1:]
root = Path(root)
build_script = Path(build_script).resolve(strict=True)

def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()

binaries = {}
for path in sorted((root / "bin").iterdir()):
    resolved = path.resolve(strict=True)
    binaries[path.name] = {
        "path": str(path),
        "resolved_path": str(resolved),
        "sha256": sha(resolved),
    }
receipt = {
    "schema_version": 1,
    "slurm_job_id": job,
    "km_revision": km_revision,
    "rustdl_revision": rustdl_revision,
    "sequoia_revision": sequoia_revision,
    "build_script": str(build_script),
    "build_script_sha256": sha(build_script),
    "sbt_launcher_sha256": sbt_sha,
    "ablation_patches_manifest": str(root / "ablation-patches.sha256"),
    "ablation_patches_manifest_sha256": sha(root / "ablation-patches.sha256"),
    "toolchain": {
        "cargo": subprocess.check_output(["/home/hohndor/.cargo/bin/cargo", "--version"], text=True).strip(),
        "rustc": subprocess.check_output(["/home/hohndor/.cargo/bin/rustc", "--version", "--verbose"], text=True).strip(),
        "rustdl_cargo": subprocess.check_output(["/home/hohndor/.cargo/bin/rustup", "run", "1.95.0", "cargo", "--version"], text=True).strip(),
        "rustdl_rustc": subprocess.check_output(["/home/hohndor/.cargo/bin/rustup", "run", "1.95.0", "rustc", "--version", "--verbose"], text=True).strip(),
        "java": subprocess.check_output(["/ibex/scratch/hohndor/km/bench/jdk8u492-b09/bin/java", "-version"], stderr=subprocess.STDOUT, text=True).strip(),
    },
    "binaries": binaries,
}
(root / "build-receipt.json").write_text(
    json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
with (root / "binaries.sha256").open("w", encoding="utf-8") as out:
    for name, row in sorted(binaries.items()):
        out.write(f"{row['sha256']}  {name}\n")
print(json.dumps(receipt, sort_keys=True))
PY

/usr/bin/printf 'BUILD_COMPLETE root=%s job=%s\n' "$build_root" "$SLURM_JOB_ID"
