#!/bin/bash
# Build the explicit-equivalence query-collapse candidate on a compute node.
#SBATCH --job-name=km-query-eq-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/query-equivalence-20260731/build-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/query-equivalence-20260731
work=${SLURM_TMPDIR:-/tmp}/km-query-eq-build-${SLURM_JOB_ID}
archive=$root/source.tar.gz
expected_source=cff55e2a8d1df8792e2d9a1887ab76321afaea1ff7f7326bdc571477f08206ce
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=$work/target
export CARGO_TERM_COLOR=never
export LC_ALL=C

test "$(/usr/bin/sha256sum "$archive" | /usr/bin/cut -d' ' -f1)" = "$expected_source"
/usr/bin/mkdir -p "$work/source" "$CARGO_TARGET_DIR"
/usr/bin/tar -xzf "$archive" -C "$work/source"
cd "$work/source/engine"
/usr/bin/nice -n 5 cargo build --release --locked --bin km --jobs 16
"$CARGO_TARGET_DIR/release/km" routes >/dev/null
/usr/bin/install -m 0555 "$CARGO_TARGET_DIR/release/km" "$root/km.tmp"
/usr/bin/sha256sum "$root/km.tmp" | /usr/bin/cut -d' ' -f1 >"$root/km.sha256.tmp"
/usr/bin/mv "$root/km.tmp" "$root/km"
/usr/bin/mv "$root/km.sha256.tmp" "$root/km.sha256"
echo "BUILD_COMPLETE source=$expected_source binary=$(cat "$root/km.sha256")"
