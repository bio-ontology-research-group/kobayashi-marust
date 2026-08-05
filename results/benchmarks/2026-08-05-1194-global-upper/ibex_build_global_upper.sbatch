#!/bin/bash
#SBATCH --job-name=km1194-upper-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --cpus-per-task=1
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/1194-global-upper-20260805/build-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/1194-global-upper-20260805
archive=$root/source.tar.gz
expected=f0568831291e2c542fc452dc26f7a4855120721ea26a5b0137e5b549803ea874
test "$(sha256sum "$archive" | cut -d' ' -f1)" = "$expected"

src=$root/source-$SLURM_JOB_ID
mkdir "$src"
tar -xzf "$archive" -C "$src"
export PATH=/home/hohndor/.cargo/bin:/usr/bin:/bin
export CARGO_TARGET_DIR=${SLURM_TMPDIR:-$root}/target-$SLURM_JOB_ID
export CARGO_TERM_COLOR=never
cd "$src/engine"
nice -n 5 cargo build --release --bin km --jobs 1
install -m 0755 "$CARGO_TARGET_DIR/release/km" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
"$root/km" routes >/dev/null
echo "BUILD_COMPLETE archive_sha256=$expected binary_sha256=$(cut -d' ' -f1 < "$root/km.sha256")"
