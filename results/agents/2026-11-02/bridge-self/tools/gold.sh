#!/bin/bash
# gold.sh SEEDDIR GOLDDIR : HermiT answers for every seed, two JVMs at a time.
SEEDS=$1; GOLD=$2
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/oracle
one() { st=$(basename $1 .ofn); [ -s $GOLD/$st.json ] && return; (cd $O && timeout 300 java -Xmx2g -XX:-CreateCoredumpOnCrash -cp .:$(cat cp.txt) Oracle $1 > $GOLD/$st.tmp 2>/dev/null) && python3 -c "import json,sys;json.load(open(sys.argv[1]))" $GOLD/$st.tmp 2>/dev/null && mv $GOLD/$st.tmp $GOLD/$st.json; rm -f $GOLD/$st.tmp; }
export -f one; export O GOLD
ls $SEEDS/*.ofn | xargs -P 2 -I{} bash -c 'one {}'
