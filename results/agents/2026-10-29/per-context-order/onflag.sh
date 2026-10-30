#!/bin/bash
f=$2; n=$(basename $f .owl); r=$(KM_NOMINALS=1 timeout 60 $1 ofn $f 2>/dev/null | python3 -I SCRATCH/classify_on.py 2>/dev/null); echo -e "$n\t${r:-ERR}"
