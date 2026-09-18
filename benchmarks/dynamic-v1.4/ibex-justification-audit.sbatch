#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=04:00:00
#SBATCH --job-name=km-justification-audit
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
mkdir -p justification-audit/classes
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes
javac -cp "$runtime/classifier-hermit.jar" -d justification-audit/classes DynamicBenchmark.java JustificationBenchmark.java JustificationSupportAudit.java
java -XX:ActiveProcessorCount=1 -Xmx16g -cp "justification-audit/classes:$runtime/classifier-hermit.jar" org.kmbenchmark.JustificationSupportAudit justification-main/results justification-audit/normalized-supports.tsv
python3 audit_justification_main.py justification-main justification-audit/audit.json --normalized justification-audit/normalized-supports.tsv
sha256sum JustificationSupportAudit.java audit_justification_main.py "$runtime/classifier-hermit.jar" > justification-audit/audit-hashes.txt
echo JUSTIFICATION_AUDIT_COMPLETE
