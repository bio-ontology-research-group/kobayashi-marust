#!/bin/bash
# audit_seeds.sh BIN OUT.tsv FILES... : run each file on ht_bridge and auto with the
# restricted-automaton audit (KM_HT_AUTOMAT_REST_LINK_AUDIT=1); one row per run:
# file route refires(last power of two) any-miss
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sameindividual-bridge
B=$1; O=$2; shift 2
one() {
  f=$1; r=$2
  envr=(); [ "$r" != auto ] && envr=(KM_ROUTE=$r)
  e=$(env TMPDIR=$S/tmp KM_THREADS=1 "${envr[@]}" KM_HT_STATS=1 KM_HT_AUTOMAT_REST_LINK=1 KM_HT_AUTOMAT_REST_LINK_AUDIT=1 \
      KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 \
      timeout 30 $B classify --lines $f 2>&1 >/dev/null | grep AUTOMAT-REST-LINK-AUDIT)
  ref=$(echo "$e" | grep -o "refires=[0-9]*" | tail -1)
  miss=$(echo "$e" | grep -c "misses=[1-9]")
  printf "%s\t%s\t%s\t%s\n" "$f" "$r" "${ref:-refires=0}" "$miss"
}
export -f one; export B S
for f in "$@"; do echo "$f ht_bridge"; echo "$f auto"; done | xargs -P 2 -L 1 bash -c 'one $0 $1' > $O
