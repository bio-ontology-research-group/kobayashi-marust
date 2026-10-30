#!/bin/bash
env | grep "^KM_\|^RAYON" | sort > /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/rules-route-followups/capenv-$$.txt
exec ${KM_REAL_TAB} tableau "$@"
