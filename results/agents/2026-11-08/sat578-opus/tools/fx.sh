#!/bin/bash
# fx.sh BIN OUT.tsv RUNS [FAM_EXTRA]: the eight sat578 fixtures plus sat578 itself, ht_bridge and auto.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sat578-opus
export TMPDIR=$S/tmp FAM_FORCED_TIMEOUT=60 FAM_TIMEOUT=60 FAM_EXTRA="$4"
python3 -I $S/tools/fam_run.py $1 $S/fxgold $2 ht_bridge,auto $3 $S/fx/*.ofn
cut -f2,4 $2 | sort | uniq -c
