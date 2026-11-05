#!/bin/bash
# fam_all.sh BIN LABEL RUNS SPECS : the 2,000 fx seeds of the nn1811 sibling family
# (gen_fx.py, seeds 1000-2999; HermiT gold in .work/agent-scratch/cb-nn1811/fam/gold),
# RUNS runs per seed on every route in SPECS, rows to data/family-LABEL.tsv.
T=$(dirname $(readlink -f $0)); BIN=$1; L=$2; RUNS=$3; SPECS=$4
F=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-nn1811/fam
export TMPDIR=$F/../tmp FAM_THREADS=${FAM_THREADS:-1}
files=(); for g in $(ls $F/gold/fx*.json); do s=$(basename $g .json); files+=($F/seeds/$s.ofn); done
python3 -I $T/fam_run.py $BIN $F/gold $T/../data/family-$L.tsv $SPECS $RUNS "${files[@]}"
