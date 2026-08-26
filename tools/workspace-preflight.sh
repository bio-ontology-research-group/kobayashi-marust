#!/usr/bin/env bash
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
work_root="$repo_root/.work"
minimum_gib=${KM_MIN_FREE_GIB:-20}
minimum_kib=$((minimum_gib * 1024 * 1024))
available_kib=$(df -Pk "$repo_root" | awk 'NR == 2 { print $4 }')
minimum_mem_gib=${KM_MIN_AVAILABLE_MEM_GIB:-16}
minimum_mem_kib=$((minimum_mem_gib * 1024 * 1024))
available_mem_kib=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)

mkdir -p \
  "$work_root/artifacts" \
  "$work_root/inputs" \
  "$work_root/logs" \
  "$work_root/target" \
  "$work_root/tmp" \
  "$work_root/worktrees"

if (( available_kib < minimum_kib )); then
  available_gib=$((available_kib / 1024 / 1024))
  printf 'REFUSING HEAVY WORK: %s GiB free; %s GiB required.\n' \
    "$available_gib" "$minimum_gib" >&2
  exit 1
fi

if (( available_mem_kib < minimum_mem_kib )); then
  available_mem_gib=$((available_mem_kib / 1024 / 1024))
  printf 'REFUSING HEAVY WORK: %s GiB memory available; %s GiB required.\n' \
    "$available_mem_gib" "$minimum_mem_gib" >&2
  exit 1
fi

printf 'Workspace: %s\n' "$work_root"
printf 'Free space check passed: %s GiB minimum available.\n' "$minimum_gib"
printf 'Memory check passed: %s GiB minimum available.\n' "$minimum_mem_gib"
printf 'Use CARGO_TARGET_DIR=%s/target\n' "$work_root"
