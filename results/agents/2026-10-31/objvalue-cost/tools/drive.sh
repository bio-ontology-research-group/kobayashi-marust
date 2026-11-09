#!/bin/bash
# drive.sh: validation of km.f1, at most 3 KM runs at a time, one CPU each
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/objvalue-cost
./runset.sh one-f2 runs/f2-rand1k-60.tsv 60 3 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange/list-rand1k.txt nominals
./runset.sh one-f2 runs/f2-rand-10.tsv 10 3 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange/list-rand.txt nominals
./runset.sh one-f2 runs/f2-rand-auto-10.tsv 10 3 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange/list-rand.txt auto
echo ALLDONE > runs/drive.done
