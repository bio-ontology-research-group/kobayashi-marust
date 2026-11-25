#!/bin/bash
# Tests of `km-owl-reference --procedure refute` on lean/testdata/refute.
# Usage: tools/refute/test.sh BIN [WORKDIR]
#  * positive: each cert/<name>.cert is accepted on <name>.ofn;
#  * negative: each neg/<name>-<what>.cert is rejected on <name>.ofn;
#  * consistent: on cons-<name>.ofn (and consistent.ofn) the producer finds no
#    refutation and the certificate of <name> (disj for consistent.ofn) is rejected.
# Every run is under timeout 300 and ulimit -v 16000000.
set -u
bin=$(readlink -f "$1")
here=$(cd "$(dirname "$0")" && pwd)
td=$here/../../lean/testdata/refute
work=${2:-${TMPDIR:?set TMPDIR}/refute-test}
mkdir -p "$work"
fail=0; n=0
run() { ( ulimit -v 16000000; timeout 300 "$bin" --procedure refute "$@" ) 2>&1; }
accepted() { grep -q '"certified":true' <<<"$1"; }
for c in "$td"/cert/*.cert; do
  name=$(basename "$c" .cert); n=$((n+1))
  out=$(run --cert "$c" "$td/$name.ofn")
  if accepted "$out"; then echo -e "pos\t$name\tok"; else echo -e "pos\t$name\tFAIL\t$out"; fail=$((fail+1)); fi
done
for c in "$td"/neg/*.cert; do
  b=$(basename "$c" .cert); name=${b%%-*}; n=$((n+1))
  out=$(run --cert "$c" --explain "$td/$name.ofn")
  if accepted "$out"; then echo -e "neg\t$b\tFAIL (accepted)"; fail=$((fail+1)); else echo -e "neg\t$b\tok (rejected)\t$(head -c 160 <<<"$out")"; fi
done
for f in "$td"/consistent.ofn "$td"/cons-*.ofn; do
  b=$(basename "$f" .ofn); n=$((n+1))
  if [ "$b" = consistent ]; then name=disj; else name=${b#cons-}; fi
  run --print-clauses "$f" > "$work/$b.dump"
  if ( ulimit -v 16000000; timeout 300 python3 -I "$here/produce.py" "$work/$b.dump" --out "$work/$b.cert" --oracle "$bin" --ofn "$f" ) 2>/dev/null; then
    out=$(run --cert "$work/$b.cert" "$f")
    if accepted "$out"; then echo -e "cons\t$b\tFAIL (produced certificate accepted)"; fail=$((fail+1)); continue; fi
  fi
  out=$(run --cert "$td/cert/$name.cert" "$f")
  if accepted "$out"; then echo -e "cons\t$b\tFAIL (cert of $name accepted)"; fail=$((fail+1)); else echo -e "cons\t$b\tok (no certificate; cert of $name rejected)"; fi
done
echo "tests $n failures $fail"
[ $fail = 0 ]
