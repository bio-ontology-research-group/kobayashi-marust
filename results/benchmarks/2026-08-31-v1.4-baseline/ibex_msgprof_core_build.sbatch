#!/bin/bash
#SBATCH --job-name=km-v14-msgprof-core-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=8
#SBATCH --mem=16G
#SBATCH --time=00:20:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4-msgprof-core-20260901/build-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4-msgprof-core-20260901
archive=$root/v14-msgprof-core-source.tar.gz
expected=4532872d88c04979663411075ddf1a85d658115fb3e8d38cf77823a5cb49ae8e
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
