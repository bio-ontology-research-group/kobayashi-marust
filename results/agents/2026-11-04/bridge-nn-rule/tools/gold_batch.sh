#!/bin/bash
# gold_batch.sh SEEDDIR GOLDDIR [CAP] : HermiT answers through OracleBatch
# (HermiT 1.4 oracle of .work/agent-scratch/r3-unannounced/oracle), one seed
# per JVM, two JVMs at a time, CAP seconds per seed (default 30). Seeds
# without an answer within the cap get no gold and are left out of every
# comparison.
SEEDS=$1; GOLD=$2; CAP=${3:-30}
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/oracle
B=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-rule/oracle-build
CP=$O:$B:$(cat $O/cp.txt)
export CP GOLD CAP
ls $SEEDS/*.ofn | xargs -n 1 -P 2 bash -c 'st=$(basename $0 .ofn); [ -s $GOLD/$st.json ] && exit 0; timeout -k 5 $CAP java -Xmx2g -XX:-CreateCoredumpOnCrash -cp $CP OracleBatch $GOLD "$0" 2>/dev/null; true'
rm -f $GOLD/*.tmp
echo "gold: $(ls $GOLD/*.json | wc -l) of $(ls $SEEDS/*.ofn | wc -l)"
