#!/bin/bash
# gold_batch.sh SEEDDIR GOLDDIR : HermiT answers through OracleBatch, 50 seeds
# per JVM, two JVMs at a time, 600 s per batch. Seeds left without an answer
# (a batch timed out) are retried one per JVM with a 300 s cap.
SEEDS=$1; GOLD=$2
O=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/oracle
B=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-s974/oracle-build
CP=$O:$B:$(cat $O/cp.txt)
export CP GOLD
ls $SEEDS/*.ofn | xargs -n 50 -P 2 bash -c 'timeout 600 java -Xmx2g -XX:-CreateCoredumpOnCrash -cp $CP OracleBatch $GOLD "$@" 2>/dev/null' _
for f in $SEEDS/*.ofn; do st=$(basename $f .ofn); [ -s $GOLD/$st.json ] && continue
  timeout 300 java -Xmx2g -XX:-CreateCoredumpOnCrash -cp $CP OracleBatch $GOLD $f 2>/dev/null; done
rm -f $GOLD/*.tmp
echo "gold: $(ls $GOLD/*.json | wc -l) of $(ls $SEEDS/*.ofn | wc -l)"
