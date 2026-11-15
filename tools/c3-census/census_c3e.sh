#!/bin/bash
# fragment check of sroiq-c2a on each listed input, 60 s each, P at a time
# usage: census.sh BIN LIST OUT [P]
export B=$1
export C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
export TMPDIR=/mnt/data1/leechuck/km-work/v170/scratch/c3e/tmp
one() {
  o=$1
  out=$( { /usr/bin/time -f "%e" timeout 60 $B --procedure sroiq-c2a --check $C/$o.owl; } 2>&1 )
  rc=$?
  printf '%s\t%s\t%s\n' "$o" "$rc" "$(echo "$out" | tr '\n' ' ' | cut -c1-300)"
}
export -f one
xargs -P ${4:-3} -I{} bash -c 'one {}' < "$2" > "$3"
