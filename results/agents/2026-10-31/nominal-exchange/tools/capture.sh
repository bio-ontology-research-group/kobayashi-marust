#!/bin/bash
# capture.sh: KM_ENGINE_BIN wrapper; saves engine stdin, args and KM_* env, then runs the real engine
N=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange/cap
mkdir -p $N; k=$(date +%s%N)
env | grep '^KM_' | grep -v KM_ENGINE_BIN > $N/$k.env; echo "$@" > $N/$k.args
tee $N/$k.json | $CAP_REAL engine "$@"
