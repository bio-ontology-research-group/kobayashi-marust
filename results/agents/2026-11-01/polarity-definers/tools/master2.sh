#!/bin/bash
S=$S; N=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange
cd $S
while kill -0 2459820 2>/dev/null; do sleep 15; done
echo "chunk aa done $(date)" >> master.log
./tools/dataset.sh new probes fixtures tnd-sorts tnd-fresh2 tnd-fresh3 nomdata-forced nomdata-auto r3data-auto r1600-auto > runs/dataset-new.log 2>&1
echo "data done $(date)" >> master.log
cut -f1 runs/new-rand1k-nominals-60.tsv | sed 's#.*/seeds/#seeds/#' | sort -u > runs/rand1k-done.txt
grep -v -x -F -f runs/rand1k-done.txt $N/list-rand1k.txt > runs/rand1k-rest.txt
./tools/runset.sh tools/pin-new runs/new-rand1k-nominals-60.tsv 60 nominals runs/rand1k-rest.txt
echo "rand1k done $(date)" >> master.log
./tools/runset.sh tools/pin-new runs/new-rand-nominals-10.tsv 10 nominals $N/list-rand.txt
echo "rand nominals done $(date)" >> master.log
./tools/runset.sh tools/pin-new runs/new-rand-auto-10.tsv 10 auto $N/list-rand.txt
echo "ALLDONE $(date)" >> master.log
