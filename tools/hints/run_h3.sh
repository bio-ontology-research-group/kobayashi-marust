#!/bin/bash
# usage: run_h3.sh LIST OUTROOT [P] [driver args...]
# LIST: input names in column 1 (as tools/hints/results/sample.tsv); at most P at a time.
C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
D=/mnt/data1/leechuck/km-work/wt/v170-plugin/tools/hints/driver_h3.py
export TMPDIR=/mnt/data1/leechuck/km-work/v170/scratch/h3/tmp
LIST=$1
export C D OUT=$2
P=${3:-2}
shift 3
export DARGS="$*"
one() {
  o=$1
  [ "${H3_FORCE:-0}" != 1 ] && [ -f $OUT/$o/result.json ] && exit 0
  mkdir -p $OUT/$o
  timeout 2400 python3 $D $C/$o.owl $OUT/$o $DARGS > $OUT/$o/driver.out 2> $OUT/$o/driver.err
  [ -f $OUT/$o/result.json ] || echo "{\"input\": \"$o\", \"status\": \"driver-timeout\"}" > $OUT/$o/result.json
  # keep every evidence file and km.lines under 50 MB
  find $OUT/$o \( -name '*.hint' -o -name '*.wit' -o -name 'classes.txt' -o -name 'km.lines' \) -size +50M -delete
  find $OUT/$o -name 'check*.jsonl' -size +5M -delete
  find $OUT/$o \( -name 'base.cl' -o -name 'base.idx' \) -size +5M -delete
}
export -f one
cut -f1 $LIST | xargs -P $P -I{} bash -c 'one {}'
