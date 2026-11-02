#!/bin/bash
# tests.sh WORKTREE OUTDIR RUNS : the full library suite RUNS times and every
# integration target once, KM_THREADS=1, --test-threads=1, no other KM_*
# variable in the environment (the release flags change two configuration
# premises of bridge tests; docs/HYBRID-CB-HT.md section 19.5).
W=$1; O=$2; N=${3:-3}; mkdir -p $O
cd $W/engine
for k in $(env | grep -o '^KM_[A-Z_]*'); do unset $k; done
export KM_THREADS=1 CARGO_TARGET_DIR=$W/engine/target TMPDIR=$W/.scratch
for i in $(seq 1 $N); do
  nice cargo test --release --lib -- --test-threads=1 > $O/lib$i.log 2>&1
  grep -E "^test .*FAILED$" $O/lib$i.log | sed 's/ \.\.\. FAILED//; s/^test //' | sort > $O/lib$i.failures
  echo "lib run $i: $(grep -E '^test result' $O/lib$i.log)" >> $O/summary.txt
done
: > $O/integ.txt
for t in tests/*.rs; do st=$(basename $t .rs)
  r=$(nice cargo test --release --test $st -- --test-threads=1 2>&1 | grep -E "^test result" | tail -1); echo "$st $r" >> $O/integ.txt; done
echo "integration targets: $(wc -l < $O/integ.txt), failing: $(grep -vc 'result: ok' $O/integ.txt)" >> $O/summary.txt
echo DONE >> $O/summary.txt
