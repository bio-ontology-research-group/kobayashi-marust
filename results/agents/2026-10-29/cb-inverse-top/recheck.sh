#!/bin/bash
# Rerun the ENV/ERR seeds of each r2 result file one at a time and splice the new lines in.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-inverse-top; cd $S; source $S/env.sh
for f in r2/*.txt; do
  n=$(basename $f .txt); b=$(echo $n | cut -d_ -f2); r=$(echo $n | cut -d_ -f3)
  awk '$2=="ENV"||$2=="ERR"{print $1}' $f > r2/$n.retry; [ -s r2/$n.retry ] || continue
  if [[ $n == f300* ]]; then export SQ= SEEDS=$S/fresh/seeds GOLD=$S/fresh/gold; else source $S/env.sh; fi
  extra=""; [ $r = htb ] && extra="KM_ROUTE=ht_bridge"
  SEEDLIST=r2/$n.retry J=2 python3 -I eval.py $S/km.$b 0 0 r2/$n.retried $extra
  python3 - $f r2/$n.retried <<'PY'
import sys
main=[l.rstrip("\n") for l in open(sys.argv[1])]; new={l.split()[0]:l.rstrip("\n") for l in open(sys.argv[2])}
open(sys.argv[1],"w").write("\n".join(new.get(l.split()[0],l) for l in main)+"\n")
PY
done
for f in r2/*.txt; do echo "$(basename $f): $(awk '{print $2}' $f | sed 's/(.*//' | sort | uniq -c | tr '\n' ' ')"; done
