#!/bin/bash
# five.sh BIN: the five R3 seeds on forced bridge and auto, against HermiT
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
cd $S/bridge-merge-edges
DIFF_KEEP=KM_THREADS=1 DIFF_THREADS=3 DIFF_KM_TIMEOUT=${T:-120} python3 -I $S/bridge-nominal-merge/diff_run.py $1 $S/r3-unannounced/oracle $S/r3-unannounced/gold $2 ht_bridge,auto $S/r3-unannounced/seeds/{r1164,r281,r947,r2627,r2970}.ofn
