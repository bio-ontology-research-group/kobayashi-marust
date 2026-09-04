#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=8G
#SBATCH --array=0-11%4
#SBATCH --job-name=km-impact-baselines

set -euo pipefail
: "${IMPACT_ROOT:?set IMPACT_ROOT}"
: "${PAPER_ROOT:?set PAPER_ROOT}"
benchmark=/ibex/scratch/hohndor/km/paper-benchmark-20260830
tools="$benchmark/runner-tools"
cases="$PAPER_ROOT/paper/impact/cases"
names=(hidden-full-dl-negative hidden-full-dl-positive snomed-style-negative snomed-style-positive access-control-negative access-control-positive)
reasoners=(elk hermit)
reasoner_index=$((SLURM_ARRAY_TASK_ID / 6))
case_index=$((SLURM_ARRAY_TASK_ID % 6))
reasoner=${reasoners[$reasoner_index]}
name=${names[$case_index]}
case "$reasoner" in
  elk) jar="$benchmark/runtimes/classifier-elk.jar"; factory=org.semanticweb.elk.owlapi.ElkReasonerFactory ;;
  hermit) jar="$benchmark/runtimes/classifier-hermit.jar"; factory=org.semanticweb.HermiT.ReasonerFactory ;;
esac
PYTHONPATH="$tools" python3 "$tools/run_java_one.py" \
  --baseline "$reasoner" --factory "$factory" --jar "$jar" \
  --ontology "$cases/$name.ofn" --ontology-id "$name" \
  --output-root "$IMPACT_ROOT/baselines" --tools-root "$tools" \
  --timeout 300 --memcap-mb 6144
test -s "$IMPACT_ROOT/baselines/$reasoner/$name.result.json"
