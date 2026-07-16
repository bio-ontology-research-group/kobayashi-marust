#!/bin/bash
#SBATCH --job-name=km-auto-analyze
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/auto-analyze-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715
: "${EXPECTED_KM_SHA:?submit with EXPECTED_KM_SHA set to km-auto-final SHA-256}"
/usr/bin/python3 "$root/analyze_auto.py" --root "$root" \
  --expected-km-sha "$EXPECTED_KM_SHA" \
  --expected-konclude-sha 5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3 \
  --expected-canonicalizer-sha 2fc28764e34418ae3004f6dca7bb9bb6c6f763b022b0d356b80f896fa18173a2 \
  --expected-profile-sha c6d9bb025d829b0541286d3868adfd965501b24988f0898f6b23ecdd537c1c23 \
  --expected-list-sha 7849b4b875d3b9bc5e214b67a1fa584f3d684e595954ca11a816448c87d3d2b8 \
  --expected-runner-sha fd372c4593e3ea48fec93b3f06656c4e8479783047d5dc7ff30b901aed54d119
