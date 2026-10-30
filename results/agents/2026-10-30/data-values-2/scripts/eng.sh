#!/bin/bash
# usage: eng.sh <km> <clauses.json> <envfile> <tag> [extra env...]; runs `km engine` directly
km=$1; cl=$2; envf=$3; tag=$4; shift 4
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-values-2
mkdir -p $S/eng/out
env -i PATH=/usr/bin:/bin HOME=$HOME TMPDIR=$S/tmp $(grep -v SUPERVISOR_PID $envf | grep -v KM_TIMING) KM_STATS=1 "$@" /usr/bin/time -f "%e s %M KB" timeout ${TO:-300} $km engine < $cl > $S/eng/out/$tag.out 2> $S/eng/out/$tag.err
echo "== $tag rc=$? $(tail -1 $S/eng/out/$tag.err)"; grep "KM_STATS" $S/eng/out/$tag.err | head -5
