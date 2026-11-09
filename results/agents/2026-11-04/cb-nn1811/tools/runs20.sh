#!/bin/bash
# runs20.sh BIN LABEL [SPECS] : the target seeds (nn1811, its reductions r*, the nominal
# CB gap m*, fx12), 20 runs each on every route in SPECS (default ht_bridge,auto), compared
# with the HermiT answers copied to .work/agent-scratch/cb-nn1811/tgt/gold. Rows go to
# data/targets-LABEL.tsv (file, route, run, verdict, seconds, detail).
T=$(dirname $(readlink -f $0)); BIN=$1; L=$2; SPECS=${3:-ht_bridge,auto}
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-nn1811/tgt
OUT=$T/../data/targets-$L.tsv; : > $OUT
export TMPDIR=$S/../tmp
python3 -I $T/fam_run.py $BIN $S/gold $OUT $SPECS 20 $(ls $S/seeds/*.ofn)
python3 -I - $OUT <<'P'
import sys, collections
c = collections.Counter(); t = collections.defaultdict(float)
for l in open(sys.argv[1]):
    f, spec, run, v, s, d = l.rstrip('\n').split('\t')
    k = (f.split('/')[-1], spec); c[(k, v)] += 1; t[k] = max(t[k], float(s))
for k in sorted({k for k, _ in c}):
    print('%-12s %-10s %s  max %.2fs' % (k[0], k[1], ' '.join('%s=%d' % (v, n) for (kk, v), n in sorted(c.items()) if kk == k), t[k]))
P
