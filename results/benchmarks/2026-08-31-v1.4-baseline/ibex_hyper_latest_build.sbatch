#!/bin/bash
#SBATCH --job-name=km-v14-hyper-latest-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=8
#SBATCH --mem=16G
#SBATCH --time=00:20:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-hyper-latest-20260901/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-hyper-latest-20260901
archive=$root/v14-hyper-latest-source.tar.gz
expected=7a4c4456877d42b6f21da6938e583a82d1bb757f7b67b4c70f029f46485f16d4
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
rm -rf "$root/source"
mkdir -p "$root/source" "$root/target"
tar -xzf "$archive" -C "$root/source"
cd "$root/source/engine"
CARGO_TARGET_DIR="$root/target" cargo build --release --bin km
install -m 755 "$root/target/release/km" "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
test -x "$root/km"
cat "$root/km.sha256"
