#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --time=00:20:00
set -euo pipefail
cd /ibex/scratch/hohndor/km/v143-harness-20260918
curl --fail --location --retry 3 --max-time 600 https://github.com/MaastrichtU-IDS/rustdl/releases/download/v0.4.28/rustdl-x86_64-unknown-linux-musl -o rustdl-v0.4.28.part
echo '20b31b3f53474e95e533e0eae84d7d85da48be6987599f4ba6ee947e65ab6bea  rustdl-v0.4.28.part' | sha256sum -c -
mv rustdl-v0.4.28.part rustdl-v0.4.28
chmod +x rustdl-v0.4.28
./rustdl-v0.4.28 --version
