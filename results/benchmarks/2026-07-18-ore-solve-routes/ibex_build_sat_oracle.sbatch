#!/bin/bash
# Build the targeted HermiT satisfiability oracle on a compute node.
#SBATCH --job-name=km-build-sat-oracle
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=2G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718/slurm/build-sat-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
validation=$km_root/routing_20260715/tail-validation-20260718
source=$validation/SatisfiabilityOracle.java
classes=$validation/classes
javac=$km_root/bench/jdk8u492-b09/bin/javac
classpath=$km_root/bench/hermit_cp/'*'

/usr/bin/mkdir -p "$classes"
"$javac" -source 8 -target 8 -cp "$classpath" -d "$classes" "$source"
/usr/bin/sha256sum "$source" "$classes/SatisfiabilityOracle.class" > "$validation/sat-oracle.sha256"
/usr/bin/printf 'DONE class=%s host=%s\n' "$classes/SatisfiabilityOracle.class" "$(hostname)"
