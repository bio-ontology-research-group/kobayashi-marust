#!/bin/bash
o=$1; p=$2
r=$(timeout 60 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/ht-card-complement/km-final profile $p 2>/dev/null | python3 -c "import json,sys
try: print(json.load(sys.stdin)['selected_route'])
except Exception: print('ERR')")
echo "$o $r"
