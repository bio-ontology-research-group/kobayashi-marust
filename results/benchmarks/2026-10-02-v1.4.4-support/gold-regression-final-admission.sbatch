#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=03:00:00
#SBATCH --export=NONE
#SBATCH --job-name=km-v144-gold-regression
#SBATCH --array=0-18%4
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v144-support-recovery-20261003/gold-regression-final-admission-%A_%a.log
set -euo pipefail
/usr/bin/python3 /ibex/scratch/projects/c2014/hohndor/km/v144-support-recovery-20261003/gold-regression-final-admission.py
