#!/bin/bash
# Diagnose elc throughput on the (near-)EL giants: does elc converge if given
# more time? where does it spend time? 15803=pure-EL (el_rbox_safe), 7246/7581
# =not-EL-safe (does elc exit 3, or run the certificate path?).
#SBATCH --job-name=km_elcd
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=0:40:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=44G
#SBATCH --output=/ibex/scratch/hohndor/km/elcdiag-%j.out
set -u
module load python/3.11.0 2>/dev/null
KM=/ibex/scratch/hohndor/km; cd $KM
OFN=engine/target/release/ofn; ELC=engine/target/release/elc
for o in 15803 7246 7581; do
  echo "########## ont=$o ##########"
  $OFN corpus/ore_ont_$o.owl --meta /tmp/m_$o.json > /tmp/c_$o.json 2>/dev/null
  echo "el_rbox_safe=$(python3 -c "import json;print(json.load(open('/tmp/m_$o.json'))['el_rbox_safe'])")"
  # give elc up to 360s (beyond the 240 cap) to see if it converges at all
  KM_ELC_TIMING=1 KM_ELC_DEBUG=1 KM_ELC_RESIDUE_STATS=1 \
    timeout 360 $ELC < /tmp/c_$o.json > /tmp/o_$o.json 2>/tmp/elc_$o.err
  rc=$?
  echo "elc rc=$rc (124=timeout, 3=not-EL)"
  echo "--- elc stderr (timing/debug) ---"; tail -25 /tmp/elc_$o.err
  echo "subs_out_bytes=$(wc -c < /tmp/o_$o.json)"
  rm -f /tmp/c_$o.json /tmp/o_$o.json
done
echo "=== DONE ==="
