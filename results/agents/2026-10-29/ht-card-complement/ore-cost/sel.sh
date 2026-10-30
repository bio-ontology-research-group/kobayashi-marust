#!/bin/bash
o=$1; p=$2
timeout 60 /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/ht-card-complement/km-final profile $p 2>/dev/null | python3 -c "
import json,sys
d=json.load(sys.stdin); e=d['profile']['expressivity']
card=(e['cardinality'] or e['qualified_cardinality'] or e['functionality'])
print('$o', d['selected_route'], int(card), int(e['datatype']), int(e['inverse']), int(e['nominal']))"
