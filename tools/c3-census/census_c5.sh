#!/bin/bash
# fragment check of a route (sroiq-c2a or sroiq-hint) on each listed input, 60 s each, P at a time
# usage: census_c5.sh BIN ROUTE LIST OUT [P]
export B=$1 R=$2
export C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
export TMPDIR=/mnt/data1/leechuck/km-work/v170/scratch/c5/tmp
one() {
  o=$1
  out=$( { /usr/bin/time -f "%e" timeout 60 $B --procedure $R --check $C/$o.owl; } 2>&1 )
  rc=$?
  printf '%s\t%s\t%s\n' "$o" "$rc" "$(echo "$out" | tr '\n' ' ' | cut -c1-300)"
}
export -f one
xargs -P ${5:-3} -I{} bash -c 'one {}' < "$3" > "$4"
