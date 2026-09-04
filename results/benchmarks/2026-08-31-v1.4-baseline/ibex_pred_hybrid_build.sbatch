#!/bin/bash
#SBATCH --job-name=km-v14-pred-hybrid-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=8
#SBATCH --mem=16G
#SBATCH --time=00:20:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-pred-hybrid-20260901/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-pred-hybrid-20260901
archive=$root/v14-pred-hybrid-source.tar.gz
expected=9c13cf66d7b39931ffe606923eb218f25f790a1ca4bb84e8134f39d8260a8732
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
rm -rf "$root/source"
mkdir -p "$root/source"
tar -xzf "$archive" -C "$root/source"
cd "$root/source/engine"
# Reuse the immediately preceding candidate's target directory. Dependencies
# and unchanged code are hash-checked by Cargo; only this source delta relinks.
CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v1.4-trie-retain-20260901/target \
  cargo build --release --bin km
install -m 755 /ibex/scratch/hohndor/km/v1.4-trie-retain-20260901/target/release/km "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
test -x "$root/km"
cat "$root/km.sha256"
