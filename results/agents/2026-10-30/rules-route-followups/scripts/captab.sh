#!/bin/bash
f=${CAP_DIR:-/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/rules-route-followups/cap}/${CAP_TAG:-x}-$(date +%s%N)-$$
${KM_REAL_TAB:-/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/review-inert-sorts/km-review} tableau "$@" 2> "$f.err"
rc=$?; echo $rc > "$f.rc"; if [ $rc = 0 ]; then rm -f "$f.err" "$f.rc"; fi; exit $rc
