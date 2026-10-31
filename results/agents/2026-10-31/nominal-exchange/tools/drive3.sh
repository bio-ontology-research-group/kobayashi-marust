#!/bin/bash
# drive3.sh: final validation of the merged head (km.x3), at most 3 KM runs at a time, one CPU each
N=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange
cd $N
until [ -x km.x3 ]; do sleep 30; done
./runset.sh one-x3 runs/x3-rand1k-60.tsv 60 3 list-rand1k.txt
awk -F'\t' '$3!="ok"{print $1}' runs/x3-rand1k-60.tsv | sort -u > runs/x3-rand1k-notok.txt
./runset.sh one-v6 runs/v6-notok-60.tsv 60 3 runs/x3-rand1k-notok.txt
./runset.sh one-final2 runs/final2-notok-60.tsv 60 3 runs/x3-rand1k-notok.txt
./runset.sh one-x3 runs/x3-tpl-20.tsv 20 3 list-tpl.txt
./runset.sh one-x3 runs/x3-tpl2-20.tsv 20 3 list-tpl2.txt
./runset.sh one-x3 runs/x3-rand-10.tsv 10 3 list-rand.txt
./open.sh one-x3 x3
mkdir -p ore
(taskset -c 50 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-nominal-exchange/results/agents/2026-10-30/r3-unannounced/ore_time.sh $N/km.x3 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-nominal-exchange/results/agents/2026-10-30/r3-unannounced/ore-design-nominal.txt ore x3) &
(taskset -c 51 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-nominal-exchange/results/agents/2026-10-30/r3-unannounced/ore_time.sh $N/../nominal-r1600/km.v6 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-nominal-exchange/results/agents/2026-10-30/r3-unannounced/ore-design-nominal.txt ore v6) &
wait
echo ALLDONE > runs/drive3.done
