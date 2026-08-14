#!/bin/bash
#SBATCH --job-name=km-cert-el-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814/build-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export CARGO_TERM_COLOR=never
cd "$root/source"
nice -n 5 cargo build --release --locked --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km.ibex.tmp"
"$root/km.ibex.tmp" routes >/dev/null
mv "$root/km.ibex.tmp" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
echo "BUILD_COMPLETE binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
