#!/bin/bash
#SBATCH --job-name=km160-javachk
#SBATCH --partition=batch
#SBATCH --account=pi-hohndor
#SBATCH --cpus-per-task=8
#SBATCH --mem=96G
#SBATCH --time=16:00:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111/logs/java-checkers-%j.log
# Java step and checker step of v1.6.0-rc1 on Ibex with the PGO binary
# (tools/java-step-ibex.sh, tools/checkers-step-ibex.sh: the v1.5.5 scripts with Ibex Maven).
set -uo pipefail
module load python/3.11.0 java/24.0.2 maven/3.9.1 >/dev/null 2>&1
cd /ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111
export PATH=/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin:$HOME/.rustup/toolchains/1.95.0-x86_64-unknown-linux-gnu/bin:$PATH
export RUSTUP_TOOLCHAIN=1.95.0-x86_64-unknown-linux-gnu
KM=/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111/pgo/km-v1.6.0-rc-pgo
rm -f src/protege/target/kobayashi-marust-protege-*.jar
bash tools/java-step-ibex.sh ctl $KM > logs/java-step.log 2>&1; echo "java exit $?"; tail -2 logs/java-step.log
bash tools/checkers-step-ibex.sh ctl $KM ctl/checker-step > logs/checkers-step.log 2>&1; echo "checkers exit $?"; tail -5 logs/checkers-step.log
echo JAVACHK-DONE
