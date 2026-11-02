#!/bin/bash
# closure_audit.sh BIN OUT.tsv FILES... : run each file on ht_bridge and auto with the
# restricted automaton arm on and the fixpoint closure audit
# (KM_HT_AUTOMAT_CLOSURE_AUDIT=1). One row per run:
# file route closure-runs closure-misses transient-refires exit-status
# Extra environment for every run: AUDIT_ENV="K=V K2=V2".
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-abox-probes
B=$1; O=$2; shift 2
one() {
  f=$1; r=$2
  envr=(); [ "$r" != auto ] && envr=(KM_ROUTE=$r)
  e=$(env TMPDIR=$S/tmp KM_THREADS=1 "${envr[@]}" $AUDIT_ENV KM_HT_AUTOMAT_CLOSURE_AUDIT=1 \
      KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 \
      timeout 60 $B classify --lines $f 2>&1 >/dev/null; echo "EXIT=$?")
  runs=$(echo "$e" | grep -o "CLOSURE-AUDIT runs=[0-9]*" | tail -1 | grep -o "[0-9]*$")
  miss=$(echo "$e" | grep -o "misses_total=[0-9]*" | tail -1 | grep -o "[0-9]*$")
  ex=$(echo "$e" | grep -o "EXIT=[0-9]*" | tail -1)
  printf "%s\t%s\t%s\t%s\t%s\n" "$f" "$r" "${runs:-0}" "${miss:-0}" "$ex"
}
export -f one; export B S AUDIT_ENV
for f in "$@"; do echo "$f ht_bridge"; echo "$f auto"; done | xargs -P 2 -L 1 bash -c 'one $0 $1' > $O
