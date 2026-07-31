#!/bin/bash
# Source-bound serial build for the c6ced84 EL-witness validation chain.
# The one-CPU request avoids holding validation behind the account-wide CPU
# ceiling merely to compile the candidate.
#SBATCH --job-name=km-elcw-build1
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=03:00:00
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/elc-witness-c6ced84/build-1cpu-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/routing_20260715/elc-witness-c6ced84
archive="$root/km-c6ced84.tar.gz"
expected=b5866c643fe034c99011f0d4d869d2e04147d42154d8d21c1f5215593c3b0867
test "$(sha256sum "$archive" | cut -d' ' -f1)" = "$expected"

src="$root/source-$SLURM_JOB_ID"
mkdir "$src"
tar -xzf "$archive" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR="${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID"
export CARGO_TERM_COLOR=never
cd "$src/km-c6ced84/engine"
nice -n 5 cargo build --release --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km"
"$root/km" routes >/dev/null
sha256sum "$root/km"
echo "BUILD_COMPLETE revision=c6ced84 job=$SLURM_JOB_ID"
