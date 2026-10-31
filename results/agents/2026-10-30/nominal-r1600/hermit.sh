#!/bin/bash
# hermit.sh FILE.ofn : HermiT answer json
f=$(readlink -f "$1")
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced/oracle && timeout 300 java -Xmx1g -XX:+UseSerialGC -cp .:$(cat cp.txt) Oracle "$f"
