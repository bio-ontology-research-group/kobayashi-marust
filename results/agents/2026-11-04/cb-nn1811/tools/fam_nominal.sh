#!/bin/bash
# fam_nominal.sh BIN LABEL RUNS : the `nominals` route (nominal CB stack alone, 15 s cap) on the
# fx seeds that mention an individual (ObjectHasValue, ObjectOneOf, assertions), RUNS runs per
# seed, rows to data/family-nominals-LABEL.tsv.
T=$(dirname $(readlink -f $0)); BIN=$1; L=$2; RUNS=${3:-1}
F=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-nn1811/fam
export TMPDIR=$F/../tmp FAM_THREADS=${FAM_THREADS:-1}
files=(); for g in $(ls $F/gold/fx*.json); do s=$(basename $g .json)
  grep -qE 'NamedIndividual|ObjectOneOf|ObjectHasValue|ClassAssertion|ObjectPropertyAssertion' $F/seeds/$s.ofn && files+=($F/seeds/$s.ofn); done
echo "${#files[@]} seeds with an individual"
python3 -I $T/fam_run.py $BIN $F/gold $T/../data/family-nominals-$L.tsv nominals $RUNS "${files[@]}"
