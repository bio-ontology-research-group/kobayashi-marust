#!/bin/bash
# Bounded single-ontology diagnostic for ORE 1194 on the certified-EL route.
# Production contract: 240 s wall, 20 GiB (ceiling set at 24 G so the cgroup
# kill is a diagnosis, not the thing under test).
set -u
BIN="${BIN:?set BIN to the elc binary}"
TAG="${1:?tag}"
shift
systemd-run --user --scope -q -p MemoryMax=24G -p MemorySwapMax=0 \
  /usr/bin/time -v /usr/bin/timeout --signal=INT --kill-after=10s 240 \
  env "$@" "$BIN" \
  < /tmp/1194.clauses.json > "/tmp/1194-$TAG.out" 2> "/tmp/1194-$TAG.err"
echo "exit=$? tag=$TAG"
grep -E "Maximum resident|Elapsed \(wall" "/tmp/1194-$TAG.err"
wc -c "/tmp/1194-$TAG.out"
