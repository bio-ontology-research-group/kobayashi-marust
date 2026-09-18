#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=02:00:00
#SBATCH --job-name=km-pure-dl-audit
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes/classifier-hermit.jar
mkdir classes
javac -cp "$runtime" -d classes ProfilePanelCheck.java
sha256sum pure-dl-candidates.tsv ProfilePanelCheck.java "$runtime" > provenance.sha256
java -XX:ActiveProcessorCount=1 -Xmx16g -cp "classes:$runtime" org.kmbenchmark.ProfilePanelCheck pure-dl-candidates.tsv > eligibility.tsv
