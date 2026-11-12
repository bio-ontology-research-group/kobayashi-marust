#!/bin/bash
# Stage the v1.6.1-rc1 C1/S1 measurement root from the v1.6.0 one: same
# protocol, harness scripts, manifests, v1.5.3 and Konclude artifacts; the
# rc artifact is the PGO binary of the v1.6.1 release root.
set -euo pipefail
O=/ibex/scratch/projects/c2014/hohndor/km/v160-measure-20261111
M=/ibex/scratch/projects/c2014/hohndor/km/v161-measure-20261112
R=/ibex/scratch/projects/c2014/hohndor/km/v161-release-20261112
B=$R/pgo/km-v1.6.1-rc-pgo
mkdir -p $M/binaries $M/artifacts $M/slurm $M/tmp
cp -a $O/protocol $O/inputs $O/run_release.py $O/run_konclude.py $M/
cp -a $O/artifacts/konclude.json $O/artifacts/v153.json $M/artifacts/
cp -a $O/binaries/km-v1.5.3-* $M/binaries/
S=$(sha256sum $B | cut -d' ' -f1)
cp $B $M/binaries/km-v1.6.1-rc-pgo-$S
/usr/bin/python3 - "$M" "$R" "$S" "$O" <<'PY'
import json, sys, hashlib
M, R, S, O = sys.argv[1:5]
a = json.load(open(f"{O}/artifacts/rc.json"))
commit = open(f"{R}/COMMIT").read().strip()
a["artifacts"][0].update(version=f"v1.6.1-rc-pgo-{commit[:8]}",
    path=f"{M}/binaries/km-v1.6.1-rc-pgo-{S}", sha256=S)
a["source_commit"] = commit
a["source_manifest_sha256"] = hashlib.sha256(open(f"{R}/pgo/source-manifest.json","rb").read()).hexdigest()
a["profile_sha256"] = hashlib.sha256(open(f"{R}/pgo/merged.profdata","rb").read()).hexdigest()
json.dump(a, open(f"{M}/artifacts/rc.json","w"), indent=2)
print(json.dumps(a, indent=1))
PY
for f in heldout-rc heldout-v153 heldout-konclude pool-rc; do
  sed -e 's#v160-measure-20261111#v161-measure-20261112#g' -e 's#km155-#km161-#g' $O/$f.sbatch > $M/$f.sbatch
done
cd $M
# The checksum list of the v1.6.0 run, with the rc binary and the regenerated files replaced.
grep -v -e 'binaries/km-v1.6.0' -e 'sbatch$' -e 'artifacts/rc.json' $O/files.sha256 > files.sha256
sha256sum heldout-rc.sbatch heldout-v153.sbatch heldout-konclude.sbatch pool-rc.sbatch artifacts/rc.json binaries/km-v1.6.1-rc-pgo-$S >> files.sha256
sha256sum --quiet -c files.sha256 && echo CHECKSUMS-OK
grep -n 'v160\|km155' *.sbatch || echo "no v1.6.0 references left"
