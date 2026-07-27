#!/bin/bash
# Build only the current KM revision and HermiT oracle used by this panel.
#SBATCH --job-name=km-routes47-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=04:00:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260727-solving-routes/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/full-panel-20260727-solving-routes
script_dir=$(/usr/bin/readlink -f "${SLURM_SUBMIT_DIR:?}")
[[ ! -e $root/build ]] || { echo "refusing pre-existing build root" >&2; exit 2; }
tmp_root=${SLURM_TMPDIR:?}/km-routes47-build-$SLURM_JOB_ID
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$tmp_root/target
export CARGO_TERM_COLOR=never
export CARGO_NET_GIT_FETCH_WITH_CLI=true
mkdir -p "$root/build/bin" "$root/build/receipts" "$root/build/patches" "$tmp_root"
revision=$(/usr/bin/python3 -c \
  'import full_panel_contract as c; print(c.KM_REVISION)' \
  2>/dev/null || PYTHONPATH="$script_dir" /usr/bin/python3 -c \
  'import full_panel_contract as c; print(c.KM_REVISION)')
/usr/bin/git clone --quiet https://github.com/bio-ontology-research-group/kobayashi-marust.git "$tmp_root/src"
/usr/bin/git -C "$tmp_root/src" checkout --quiet --detach "$revision"
(cd "$tmp_root/src/engine" && /usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 32)
/usr/bin/install -m 0555 "$CARGO_TARGET_DIR/release/km" "$root/build/bin/km-main"
jdk=/ibex/scratch/hohndor/km/bench/jdk8u492-b09
"$jdk/bin/javac" -cp "/ibex/scratch/hohndor/km/bench/hermit_cp/*" \
  -d "$root/build/bin" "$script_dir/FullIriHermitOracle.java"

# The shared runner has legacy required paths for removed baselines. These
# non-executable-in-contract sentinels satisfy input validation only.
/usr/bin/printf '#!/bin/sh\nexit 127\n' > "$root/build/bin/rustdl"
/usr/bin/printf '#!/bin/sh\nexit 127\n' > "$root/build/bin/sequoia-unused"
/usr/bin/chmod 0555 "$root/build/bin/rustdl" "$root/build/bin/sequoia-unused"
/usr/bin/ln -s sequoia-unused "$root/build/bin/sequoia"
(cd "$root/build" && /usr/bin/sha256sum bin/sequoia-unused > sequoia-files.sha256)
: > "$root/build/ablation-patches.sha256"

/usr/bin/python3 - "$root/build" "$revision" "$SLURM_JOB_ID" "$script_dir/ibex_build.sbatch" <<'PY'
import hashlib, json, pathlib, subprocess, sys
root, rev, job, script = map(pathlib.Path, sys.argv[1:2]) if False else sys.argv[1:]
root = pathlib.Path(root)
def sha(p):
    h=hashlib.sha256()
    with pathlib.Path(p).open("rb") as f:
        for b in iter(lambda:f.read(1<<20),b""): h.update(b)
    return h.hexdigest()
bins={}
for p in sorted((root/"bin").iterdir()):
    q=p.resolve()
    bins[p.name]={"path":str(p),"resolved_path":str(q),"sha256":sha(q)}
receipt={"schema_version":1,"slurm_job_id":job,"km_revision":rev,
         "build_script":script,"build_script_sha256":sha(script),
         "rustdl_revision":"not-in-panel","sequoia_revision":"not-in-panel",
         "binaries":bins,
         "toolchain":{"cargo":subprocess.check_output(
             ["/home/hohndor/.cargo/bin/cargo","--version"],text=True).strip(),
             "rustc":subprocess.check_output(
             ["/home/hohndor/.cargo/bin/rustc","--version","--verbose"],text=True).strip()}}
(root/"build-receipt.json").write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
with (root/"binaries.sha256").open("w") as f:
    for name,row in sorted(bins.items()): f.write(f"{row['sha256']}  {name}\n")
PY
echo "BUILD_COMPLETE revision=$revision job=$SLURM_JOB_ID"
