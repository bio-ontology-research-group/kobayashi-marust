#!/bin/bash
# fragment check of sroiq-c2a on each listed input, 60 s each, P at a time
# usage: census_sroiq.sh LIST OUT [P]
B=/mnt/data1/leechuck/km-work/wt/v170-owl/lean/.lake/build/bin/km-owl-reference
C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
one() {
  o=$1
  out=$( { /usr/bin/time -f "%e" timeout 60 $B --procedure sroiq-c2a --check $C/$o.owl; } 2>&1 )
  rc=$?
  printf '%s\t%s\t%s\n' "$o" "$rc" "$(echo "$out" | tr '\n' ' ' | cut -c1-300)"
}
export -f one; export B C
xargs -P ${3:-4} -I{} bash -c 'one {}' < "$1" > "$2"
