#!/bin/bash
#SBATCH --job-name=km161-setup
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=4
#SBATCH --mem=16G
#SBATCH --time=03:00:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v161-release-20261112/logs/setup-%j.log
# Stage the v1.6.1-rc1 certification root from the v1.6.0 one: toolchains,
# package cache, harness, inputs and tools copied; source cloned from the
# rc1 bundle at COMMIT; Lean build cache copied so the gates rebuild only
# what changed; batch scripts generated from the v1.6.0 ones.
set -euo pipefail
O=/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111
R=/ibex/scratch/projects/c2014/hohndor/km/v161-release-20261112
C=$(cat $R/COMMIT)
cd $R
for d in elan lake-packages harness inputs tools; do cp -a $O/$d $R/; done
mkdir -p ctl receipts gate-work pgo
rm -rf src; git clone -q $R/v161-rc1.bundle src; git -C src checkout -q $C; git -C src rev-parse HEAD
mkdir -p src/lean/.lake; cp -a $O/src/lean/.lake/. src/lean/.lake/
git -C src status --porcelain --untracked-files=no | head
printf '{\n "snapshot": "%s/src",\n "commit": "%s",\n "version": "1.6.1"\n}' $R $C > ctl/pins.json
for f in gates.sbatch rust.sbatch pgo.sbatch; do
  sed -e 's#v160-release-20261111#v161-release-20261112#g' -e 's#km160-#km161-#g' \
      -e 's#v1\.6\.0-rc1#v1.6.1-rc1#g' -e 's#km-v1\.6\.0-rc-pgo#km-v1.6.1-rc-pgo#g' \
      -e 's#--version 1\.6\.0#--version 1.6.1#g' $O/$f > $R/$f
done
grep -n '1\.6\.0\|v160' $R/*.sbatch || echo "no v1.6.0 references left"
echo SETUP-DONE
