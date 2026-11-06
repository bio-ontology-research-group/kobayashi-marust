#!/bin/bash
# q.sh BIN ONT [ROUTE|auto] [ENV=VALUE ...] : one classification with the
# release flags in a clean KM_* environment, printing the subsumption and
# unsatisfiable lines (sorted) and the route; used for the ablations.
BIN=$1; ONT=$2; ROUTE=${3:-auto}; shift 3
F="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
R=""; [ "$ROUTE" != auto ] && R="--route $ROUTE"
env $(env | grep -o '^KM_[A-Z_]*' | sed 's/^/-u /') $F "$@" timeout ${CAP:-60} $BIN classify --lines $R "$ONT" 2>/dev/null | grep -E '^(SUB|UNSAT|CONSISTENT|INCONSISTENT)' | sed 's|http://example.org/[a-z0-9]*#||g' | sort | tr '\n' ' '
echo " rc=${PIPESTATUS[0]}"
