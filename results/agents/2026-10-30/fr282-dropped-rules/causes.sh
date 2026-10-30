#!/bin/bash
f=$1
e=$(env -i PATH=$PATH HOME=$HOME TMPDIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/fr282-dropped-rules/home-tmp KM_TIMING=1 timeout 90 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/pgo-v154/km-pgo-use classify --lines $f 2>&1 >/dev/null)
r=$(echo "$e" | grep -c "not applied to a nominal taxonomy")
u=$(echo "$e" | grep -o "[0-9]* data-property assertion(s) stay uncarried" | cut -d' ' -f1)
x=$(echo "$e" | grep -c "rules=0")
echo -e "$(basename $f)\t$r\t${u:-0}\t$x"
