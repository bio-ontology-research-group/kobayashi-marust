#!/bin/bash
#SBATCH --job-name=km-v14-pred-hybrid2-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=8
#SBATCH --mem=16G
#SBATCH --time=00:20:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-pred-hybrid-sweep-20260901/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-pred-hybrid-sweep-20260901
archive=$root/v14-pred-hybrid-sweep-source.tar.gz
expected=6edddbbdcac2c5447f75a0c7e19ce6a401cd1eb0dc407e78d4fca12e1204e05a
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
rm -rf "$root/source"
mkdir -p "$root/source"
tar -xzf "$archive" -C "$root/source"
cd "$root/source/engine"
CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v1.4-trie-retain-20260901/target \
  cargo build --release --bin km
install -m 755 /ibex/scratch/hohndor/km/v1.4-trie-retain-20260901/target/release/km "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
test -x "$root/km"
cat "$root/km.sha256"
