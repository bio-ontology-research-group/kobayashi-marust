#!/bin/bash
# summarise a census tsv: outcomes and decline reasons
f=$1
awk -F'\t' '{r=$3; sub(/ *Command exited.*/,"",r); sub(/ [0-9.]+ *$/,"",r);
  if ($2==124) k="timeout (60 s)"; else if (r ~ /^accepted/) k="accepted";
  else { k=r; sub(/ \(first: /," (first: ",k); if (k ~ /^not C2a/) k="not C2a"; if (k ~ /^not simple/) k="not simple or not closed"; if (k ~ /^datatypes/) k="unsupported data range" }
  print k}' $f | sort | uniq -c | sort -rn
