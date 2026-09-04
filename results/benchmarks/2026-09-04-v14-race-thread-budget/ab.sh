#!/bin/bash
# usage: ab.sh <label> <binary> <ont.owl> <outjson> <errfile> [route-args...]
# Runs one classify under a 16G ceiling; prints wall_s and tree-peak MiB (50 ms sampling of all km-* processes).
label=$1; bin=$2; ont=$3; out=$4; err=$5; shift 5
base=$(basename "$bin")
( systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 /usr/bin/time -f "WALL=%e MAXRSS_KB=%M" -o "$err.time" /usr/bin/timeout 240 env KM_TIMING=1 "$bin" classify "$@" "$ont" > "$out" 2> "$err" ) &
peak=0
while kill -0 $! 2>/dev/null; do
  sum=0
  for d in /proc/[0-9]*; do
    exe=$(readlink $d/exe 2>/dev/null) || continue
    [[ "$exe" == *"$base"* ]] || continue
    rss=$(awk '/^VmRSS:/{print $2}' $d/status 2>/dev/null); sum=$((sum + ${rss:-0}))
  done
  [ $sum -gt $peak ] && peak=$sum
  sleep 0.05
done
wait
wall=$(sed -n 's/^WALL=\([0-9.]*\).*/\1/p' "$err.time")
echo "$label wall_s=$wall tree_peak_mib=$((peak/1024))"
