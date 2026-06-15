#!/bin/bash
#SBATCH --job-name=km_fa
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=0:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/prof/fa/slurm-%A_%a.out
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km
OFN=$KM/engine/target/release/ofn
mapfile -t ONTS < $KM/prof/reg/onts.txt
ID=${SLURM_ARRAY_TASK_ID:-0}
o=${ONTS[$ID]}
RESDIR=$KM/fa_res; mkdir -p "$RESDIR"
O=$KM/corpus/ore_ont_$o.owl
[ -f "$O" ] || { echo "ONT=$o MISSING" > $RESDIR/$o.res; exit 0; }
KM_ABSORB=1 $OFN "$O" 2>/dev/null | python3 -c "
import json,sys,re
o='$o'
try: d=json.load(sys.stdin)
except: print('ONT=%s PARSEFAIL'%o); sys.exit()
cl=d.get('clauses',[])
def isconc(a): return isinstance(a,dict) and a.get('concept')
def iri(a):
    c=a.get('concept'); return c[0] if isinstance(c,list) else c
def internal(s): return bool(s) and bool(re.match(r'.*(Q_|def_|__trans__|__nom__|__dr__|aux)',str(s)))
ndisj=ndint=maxh=0
for c in cl:
    cn=[a for a in c.get('head',[]) if isconc(a)]
    if len(cn)>maxh: maxh=len(cn)
    if len(cn)>=2:
        ndisj+=1
        if any(internal(iri(a)) for a in cn): ndint+=1
print('ONT=%s N_CL=%d DISJ=%d DISJ_INT=%d MAXHEAD=%d'%(o,len(cl),ndisj,ndint,maxh))
" > $RESDIR/$o.res
