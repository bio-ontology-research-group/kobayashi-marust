#!/bin/bash
# fe_one.sh FILE : km ofn with base and new under three frontend settings; prints file, setting, sha base, sha new, bytes base, bytes new, seconds
S=$S
f=$1; stem=$(basename $f); stem=${stem%.*}
for set in default nominals absorb; do
  case $set in default) E="";; nominals) E="KM_NOMINALS=1";; absorb) E="KM_ABSORB=1";; esac
  r=()
  for b in base new; do
    t0=$(date +%s.%N)
    out=$(env -i PATH=$PATH HOME=$HOME $E KM_THREADS=1 timeout 300 $S/tools/pin-$b ofn $f --meta $S/fe/$stem.$b.meta 2>/dev/null | tee >(wc -c > $S/fe/$stem.$b.len) | sha256sum | cut -c1-16)
    rc=${PIPESTATUS[0]}
    ms=$(sha256sum < $S/fe/$stem.$b.meta 2>/dev/null | cut -c1-16); rm -f $S/fe/$stem.$b.meta
    t=$(echo "$(date +%s.%N)-$t0" | bc)
    sleep 0.05; r+=("$out" "$ms" "$(cat $S/fe/$stem.$b.len)" "$t"); rm -f $S/fe/$stem.$b.len
  done
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$stem" "$set" "${r[0]}" "${r[4]}" "${r[1]}" "${r[5]}" "${r[2]}" "${r[6]}" "${r[3]}" "${r[7]}"
done
