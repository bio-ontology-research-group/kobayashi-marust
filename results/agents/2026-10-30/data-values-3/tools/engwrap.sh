#!/bin/bash
D=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values-3
n=$(date +%s%N)
tee $D/cap/$TAG.$n.in.json | KM_STATS=1 $D/$BIN engine "$@" 2> $D/cap/$TAG.$n.err
rc=${PIPESTATUS[1]}; echo "args=$* rc=$rc env=$(env | grep ^KM_ | tr '\n' ' ')" >> $D/cap/$TAG.$n.err; exit $rc
