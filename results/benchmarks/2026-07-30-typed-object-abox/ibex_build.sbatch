#!/bin/bash
# Build the source-bound candidate on an IBEX compute node for IBEX's glibc.
# The embedded hash binds the build to the archived commit.
#SBATCH --job-name=km-objabox-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/typed-object-abox-20260730/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/typed-object-abox-20260730
tmp_root=${SLURM_TMPDIR:-$root}/build-$SLURM_JOB_ID
archive=$root/km-typed-object-abox-source.tar.gz
expected=230e29341b29553aa0608264b16a142c8dd7431e2edd69eaff41d2f9609bdd2a
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$tmp_root/target
export CARGO_TERM_COLOR=never
export LC_ALL=C

test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected"
/usr/bin/mkdir -p "$tmp_root/source"
/usr/bin/tar -xzf "$archive" -C "$tmp_root/source"
source_root=$tmp_root/source/km-typed-object-abox
test -f "$source_root/engine/Cargo.toml"
cd "$source_root/engine"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16

binary=$CARGO_TARGET_DIR/release/km
"$binary" routes >/dev/null
/usr/bin/install -m 0555 "$binary" "$root/km"
/usr/bin/sha256sum "$root/km"
echo "TYPED_OBJECT_ABOX_BUILD_COMPLETE job=$SLURM_JOB_ID source_sha256=$expected"
