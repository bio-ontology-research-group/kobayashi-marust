#!/bin/bash
set -euo pipefail
tee /ibex/scratch/hohndor/km/v14-uberon-rules-tin-v2-20260904/uberon.tin.json \
  | /ibex/scratch/hohndor/km/v14-uberon-rules-profile-20260904/km-branch-profile-native tableau \
      2>>/ibex/scratch/hohndor/km/v14-uberon-rules-tin-v2-20260904/tableau.stderr.log
