#!/bin/bash
# Wait until pools.sh (PID 717355) has written bridge-nn-rule-fam.tsv, stop it
# by PID (the bash script, then its diff_run child, then that child's KM
# children and their workers, all found through the parent PID), then run
# pools2.sh on the remaining pools with a 20 s cap, two KM runs at a time.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sat578-opus
until [ -s $S/pools/fix/bridge-nn-rule-fam.tsv ]; do sleep 20; done
kill -STOP 717355
PY=$(ps -o pid= --ppid 717355 | tr -d ' ')
kill -STOP $PY 2>/dev/null
KMS=$(ps -o pid= --ppid $PY 2>/dev/null)
WORKERS=$(for k in $KMS; do ps -o pid= --ppid $k; done)
kill $WORKERS $KMS 2>/dev/null
kill -KILL $PY 717355 2>/dev/null
echo "stopped 717355 $PY $KMS $WORKERS" > $S/logs/after-families.stop
rm -f $S/pools/fix/*.part
sleep 5
cd $S && env DIFF_THREADS=2 GUARD=1 CAP=20 $S/tools/pools2.sh $S/bin/km-b1fcbb93 fix
