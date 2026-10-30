#!/bin/bash
# usage: gold.sh ORACLE GOLDDIR FILE
f=$3; stem=$(basename $f .ofn); out=$2/$stem.json
[ -s $out ] && exit 0
cd $1 && timeout 300 java -Xmx2g -cp .:$(cat cp.txt) Oracle $(readlink -f $f) 2>/dev/null > $out.tmp && python3 -c "import json,sys;json.load(open('$out.tmp'))" 2>/dev/null && mv $out.tmp $out || rm -f $out.tmp
