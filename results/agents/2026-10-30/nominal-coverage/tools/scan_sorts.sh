#!/bin/bash
# usage: scan_sorts.sh KM NAME -> NAME\t<has __data__ 0/1/err>
C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
n=$1
r=$(env -u KM_ROUTE KM_NOMINALS=1 timeout 60 ./km.base ofn $C/$n.owl 2>/dev/null | grep -c '"__data__"')
echo -e "$n\t${PIPESTATUS[0]}\t$r"
