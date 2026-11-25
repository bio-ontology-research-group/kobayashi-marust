#!/bin/bash
# fragment check of shoiq-c2a on each listed input, 60 s each, two at a time
B=/mnt/data1/leechuck/km-work/wt/v170-owl/lean/.lake/build/bin/km-owl-reference
C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
one() {
  o=$1
  out=$( { /usr/bin/time -f "%e" timeout 60 $B --procedure shoiq-c2a --check $C/$o.owl; } 2>&1 )
  rc=$?
  printf '%s\t%s\t%s\n' "$o" "$rc" "$(echo "$out" | tr '\n' ' ' | cut -c1-300)"
}
export -f one; export B C
xargs -P 2 -I{} bash -c 'one {}' < list.txt > results.tsv
