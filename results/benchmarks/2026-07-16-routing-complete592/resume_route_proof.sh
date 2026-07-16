#!/bin/bash
set -euo pipefail

km_root=/ibex/scratch/hohndor/km
proof_root=$km_root/route_proof_20260716
ontology_list=$km_root/routing_20260715/onts.txt
helper=$proof_root/resume_route_proof.py
job=$proof_root/validate_all_named_routes.sbatch

audit=$("$helper" "$proof_root" "$ontology_list")
printf '%s\n' "$audit" | tee "$proof_root/resume-audit.json"
array_spec=$(python3 -c 'import json,sys; print(json.load(sys.stdin)["array_spec"])' \
  <<<"$audit")

if [[ -z "$array_spec" ]]; then
  printf 'COMPLETE: no panels require resumption\n'
  exit 0
fi

submission=$(sbatch --parsable --array="${array_spec}%48" "$job")
printf 'RESUMED job=%s array=%s\n' "$submission" "$array_spec"
