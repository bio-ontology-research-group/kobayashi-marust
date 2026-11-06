#!/bin/bash
# run1.sh BIN ONT ROUTE [ENV=V ...] : one classification with the release flags
# in a clean KM_* environment; ROUTE is `auto` or a KM_ROUTE value. Prints
# the JSON answer on stdout, stderr to $ERR (default /dev/null).
BIN=$1; ONT=$2; ROUTE=$3; shift 3
E=(env -i PATH=$PATH HOME=$HOME KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1)
[ "$ROUTE" != auto ] && E+=(KM_ROUTE=$ROUTE)
E+=("$@")
timeout -k 5 ${CAP:-60} "${E[@]}" $BIN classify $ONT 2> ${ERR:-/dev/null}
