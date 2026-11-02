#!/bin/bash
# ore16.sh KM_BIN TAG : the 16 held-out ORE inputs of docs/V1.5.5-STATUS.md
# ("Konclude coverage gap"), one process at a time, release flags, KM_THREADS=1,
# timeout 240, km classify (JSON). Writes $S/ore/TAG/<ont>.json, .err tail,
# .time and times-TAG.tsv (ontology, rc, wall s, peak RSS KiB), then compares
# every answer with the pinned references (compare_ref.py of bridge-defers).
km=$1; tag=$2
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-m413
C=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v1.5.5/results/agents/2026-11-01/bridge-defers/tools/compare_ref.py
F=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files
O=$S/ore/$tag; mkdir -p $O $S/tmp
rm -f $O/times-$tag.tsv $O/refcmp-$tag.txt
for n in 4796 6132 9899 3917 11378 12191 9151 9577 12128 4903 11647 3087 10838 16315 7557 10926; do
  ont=ore_ont_$n
  s=$(date +%s.%N)
  env $(env | grep -o '^KM_[A-Z_0-9]*' | sed 's/^/-u /') TMPDIR=$S/tmp KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 \
    KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1 KM_TIMING=1 \
    /usr/bin/time -v -o $O/$ont.time timeout 240 $km classify $F/$ont.owl > $O/$ont.json 2> $O/$ont.err
  rc=$?; e=$(date +%s.%N)
  rss=$(awk -F: '/Maximum resident/{gsub(/ /,"",$2); print $2}' $O/$ont.time)
  tail -c 3000 $O/$ont.err > $O/$ont.errtail; rm -f $O/$ont.err
  echo -e "$ont\t$rc\t$(echo "$e - $s" | bc)\t$rss" >> $O/times-$tag.tsv
  if [ $rc -eq 0 ]; then
    (cd $S/tmp && python3 -I $C $ont $O/$ont.json $O/cmp >> $O/refcmp-$tag.txt 2>&1)
  fi
  gzip -f $O/$ont.json
done
echo DONE >> $O/times-$tag.tsv
