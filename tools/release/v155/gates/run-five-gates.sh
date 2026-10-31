#!/bin/bash
# Run the five Lean certification gates from the bound snapshot, in order,
# one at a time (capture-gate.py refuses to start beside another compiler).
cd "$(dirname "$0")"
mkdir -p ../logs
for g in elc routing ht cb rules; do
  echo "=== $g start $(date -u +%FT%TZ)" >> ../logs/five-gates.log
  nice python3 capture-gate.py --gate $g >> ../logs/five-gates.log 2>&1
  echo "=== $g exit $? $(date -u +%FT%TZ)" >> ../logs/five-gates.log
done
