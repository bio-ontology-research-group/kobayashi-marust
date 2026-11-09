#!/bin/bash
# Sequential one-core timing of the seven inputs with four binaries.
cd "$(dirname "$0")"
for i in 205 7499 7278 3726 10019 12107 5303; do
  for b in km-v153-pgo km-v154-pgo km-v154-rel km-fix; do
    CPU=${CPU:-40} TO=900 ./run1.sh ./$b inputs/ore_ont_$i.owl timing/$b-$i
  done
done
