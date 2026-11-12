#!/bin/bash
#SBATCH --job-name=km161-q2-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=16
#SBATCH --mem=96G
#SBATCH --time=04:00:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v161-q2-20261112/logs/build-%j.log
# Build km (release, mimalloc, no PGO) and km-el-reference from the bundled commit in COMMIT.
set -euo pipefail
I=/ibex/scratch/projects/c2014/hohndor/km/v161-q2-20261112
S=/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111
C=$(cat $I/COMMIT)
rm -rf $I/src; git clone -q $I/km.bundle $I/src; cd $I/src; git checkout -q $C; git rev-parse HEAD
unset PYTHONPATH LD_LIBRARY_PATH
TC=$HOME/.rustup/toolchains/1.95.0-x86_64-unknown-linux-gnu
export PATH=$TC/bin:$S/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin:$HOME/.cargo/bin:/usr/local/bin:/usr/bin:/bin
export CARGO_HOME=$HOME/.cargo RUSTUP_TOOLCHAIN=1.95.0-x86_64-unknown-linux-gnu CARGO_NET_OFFLINE=true CARGO_INCREMENTAL=0
mkdir -p lean/.lake; cp -a $S/lake-packages lean/.lake/packages; cp -a $S/src/lean/.lake/build lean/.lake/build
(cd lean && LEAN_NUM_THREADS=16 lake build km-el-reference) 2>&1 | tail -3
(cd engine && cargo build --release --features mimalloc --bin km -j 16) 2>&1 | tail -3
mkdir -p $I/bin; cp engine/target/release/km lean/.lake/build/bin/km-el-reference $I/bin/
sha256sum $I/bin/*
echo BUILD-DONE
