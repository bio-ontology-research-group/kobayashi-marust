#!/bin/bash
#SBATCH --job-name=km-v14-eq-index-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=8
#SBATCH --mem=16G
#SBATCH --time=00:20:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-eq-index-20260901/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-eq-index-20260901
archive=$root/v14-pred-sig-eq-index-source.tar.gz
expected=dd06cd0926355a2a43ecb2585762b2264f320ef33512b3d5728863e799e3f5b8
[[ $(sha256sum "$archive" | cut -d' ' -f1) == "$expected" ]]
rm -rf "$root/source"
mkdir -p "$root/source"
tar -xzf "$archive" -C "$root/source"
cd "$root/source/engine"
CARGO_TARGET_DIR=/ibex/scratch/hohndor/km/v1.4-trie-retain-20260901/target cargo build --release --bin km
install -m 755 /ibex/scratch/hohndor/km/v1.4-trie-retain-20260901/target/release/km "$root/km"
sha256sum "$root/km" > "$root/km.sha256"
test -x "$root/km"
cat "$root/km.sha256"
