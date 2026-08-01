#!/bin/bash
# Build the v0.2.0 KM binary and bind the pinned external baseline artifacts.
#SBATCH --job-name=km-v020-panel-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/release-v020-uniform-20260801/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; printf "BUILD_FAILED line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

root=/ibex/scratch/hohndor/km/release-v020-uniform-20260801
drivers=$root/drivers
build=$root/build
old=/ibex/scratch/hohndor/km/full-panel-20260722/build
revision=364b8b2ebe99ea06e8e722e5c5613422267d9ac5
tmp=${SLURM_TMPDIR:-$root/tmp-$SLURM_JOB_ID}/km-v020-build
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TERM_COLOR=never
export CARGO_NET_GIT_FETCH_WITH_CLI=true

for required in \
    "$drivers/full_panel_contract.py" \
    "$drivers/_frozen_contract_20260722.py" \
    "$old/bin/rustdl" \
    "$old/bin/sequoia" \
    "$old/bin/FullIriHermitOracle.class" \
    "$old/sequoia-files.sha256"
do
    [[ -e $required ]] || { echo "missing input: $required" >&2; exit 2; }
done

/usr/bin/mkdir -p "$build/bin" "$tmp"
/usr/bin/git clone --quiet https://github.com/bio-ontology-research-group/kobayashi-marust.git "$tmp/source"
/usr/bin/git -C "$tmp/source" checkout --quiet --detach "$revision"
[[ $(/usr/bin/git -C "$tmp/source" rev-parse HEAD) == "$revision" ]]
export CARGO_TARGET_DIR=$tmp/target
(
    cd "$tmp/source/engine"
    /usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs "$SLURM_CPUS_PER_TASK"
)
/usr/bin/install -m 0555 "$CARGO_TARGET_DIR/release/km" "$build/bin/km-main"
/usr/bin/ln -sfn "$old/bin/rustdl" "$build/bin/rustdl"
/usr/bin/ln -sfn "$old/bin/sequoia" "$build/bin/sequoia"
/usr/bin/ln -sfn "$old/bin/FullIriHermitOracle.class" "$build/bin/FullIriHermitOracle.class"
/usr/bin/ln -sfn "$old/sequoia-files.sha256" "$build/sequoia-files.sha256"

[[ $(/usr/bin/sha256sum "$build/bin/rustdl" | /usr/bin/awk '{print $1}') == \
    673c7cf8d85be46213bbd3cae5f2168f03668cbf9fb4240643be5ac63f2892db ]]
[[ $(/usr/bin/sha256sum "$build/bin/FullIriHermitOracle.class" | /usr/bin/awk '{print $1}') == \
    67858c5d94a613f28821dfb19d2170bd270af2ee0db74a1a2b9db1e759591e42 ]]
[[ $(/usr/bin/sha256sum -L "$build/bin/sequoia" | /usr/bin/awk '{print $1}') == \
    a84dfc7b30cb46dfd9333ef89ac6c2b1cd3bb27025777cc02f8c84b6df7a7649 ]]

/usr/bin/python3 - "$build" "$drivers" "$revision" "$SLURM_JOB_ID" <<'PY'
import hashlib, json, pathlib, subprocess, sys
build = pathlib.Path(sys.argv[1])
drivers = pathlib.Path(sys.argv[2])
revision = sys.argv[3]
job = sys.argv[4]
def sha(path):
    path = pathlib.Path(path).resolve(strict=True)
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()
binaries = {p.name: {"path": str(p), "resolved_path": str(p.resolve()), "sha256": sha(p)}
            for p in sorted((build / "bin").iterdir())}
drivers_h = {p.name: sha(p) for p in sorted(drivers.iterdir()) if p.is_file()}
receipt = {
    "schema_version": 1,
    "slurm_job_id": job,
    "km_revision": revision,
    "external_build_receipt": "/ibex/scratch/hohndor/km/full-panel-20260722/build/build-receipt.json",
    "binaries": binaries,
    "drivers": drivers_h,
    "toolchain": {
        "cargo": subprocess.check_output(["/home/hohndor/.cargo/bin/cargo", "--version"], text=True).strip(),
        "rustc": subprocess.check_output(["/home/hohndor/.cargo/bin/rustc", "--version", "--verbose"], text=True).strip(),
    },
}
(build / "build-receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
with (build / "binaries.sha256").open("w") as out:
    for name, row in sorted(binaries.items()):
        out.write(f"{row['sha256']}  {name}\n")
print(json.dumps(receipt, sort_keys=True))
PY

echo "BUILD_COMPLETE revision=$revision job=$SLURM_JOB_ID"
