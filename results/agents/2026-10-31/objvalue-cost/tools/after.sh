#!/bin/bash
# after.sh: once drive.sh finished, before/after times of the test case and the eight seeds (3 CPUs)
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/objvalue-cost
until [ -f runs/drive.done ]; do sleep 60; done
(./ctime.sh 44 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/objvalue-cost/km.f2 60 nominals /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/objvalue-cost/ov.ofn /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/seeds/r163.ofn /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/seeds/r219.ofn > after-a.tsv) &
(./ctime.sh 45 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/objvalue-cost/km.f2 60 nominals /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/seeds/r461.ofn /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/seeds/r481.ofn > after-b.tsv) &
(./ctime.sh 46 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/objvalue-cost/km.f2 60 nominals /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/seeds/r575.ofn /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/seeds/r696.ofn > after-c.tsv) &
wait
(./ctime.sh 44 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/objvalue-cost/km.f2 300 nominals /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/seeds/r1536.ofn > after-d.tsv) &
(./ctime.sh 45 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/objvalue-cost/km.f2 300 nominals /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/seeds/r3777.ofn > after-e.tsv) &
(./ctime.sh 46 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/objvalue-cost/km.base 300 nominals /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/seeds/r1536.ofn /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/seeds/r3777.ofn > before-de.tsv) &
wait
echo AFTERDONE > after.done
