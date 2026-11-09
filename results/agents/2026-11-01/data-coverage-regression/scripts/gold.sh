#!/bin/bash
# usage: gold.sh ORACLE_DIR GOLD_DIR FILE  -- HermiT answer of FILE cached as GOLD_DIR/<stem>.json
o=$1; g=$2; f=$(realpath $3); stem=$(basename $f .ofn)
[ -s $g/$stem.json ] && exit 0
cd $o && timeout 300 java -cp .:$(cat cp.txt) Oracle $f 2>/dev/null > $g/$stem.json.tmp && python3 -c "import json,sys;json.load(open(sys.argv[1]))" $g/$stem.json.tmp 2>/dev/null && mv $g/$stem.json.tmp $g/$stem.json || rm -f $g/$stem.json.tmp
