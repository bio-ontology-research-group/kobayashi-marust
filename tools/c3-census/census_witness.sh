#!/bin/bash
# witness-route census: --witness-route --check on each listed input, 60 s each, P at a time
# usage: census_witness.sh BIN LIST OUT [P]
export B=$1
export C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
export TMPDIR=/mnt/data1/leechuck/km-work/v170/scratch/h2/tmp
one() {
  o=$1
  out=$( { /usr/bin/time -f "%e %M" timeout 60 $B --procedure sroiq-hint --witness-route --check $C/$o.owl; } 2>&1 )
  rc=$?
  printf '%s\t%s\t%s\n' "$o" "$rc" "$(echo "$out" | tr '\n' ' ' | cut -c1-300)"
}
export -f one
xargs -P ${4:-3} -I{} bash -c 'one {}' < "$2" > "$3"
