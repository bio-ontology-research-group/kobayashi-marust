#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=4
#SBATCH --mem=12G
#SBATCH --time=02:00:00
#SBATCH --job-name=km-v143-harness-stage
set -euo pipefail
root=/ibex/scratch/hohndor/km/v143-harness-20260918
cd "$root"
sha256sum -c staging.sha256
mkdir source corpus chunks
tar -xzf harness-source.tar.gz -C source
curl --fail --location --retry 3 --max-time 1800 https://zenodo.org/api/records/18578/files/ore2015_sample.zip/content -o ore2015_sample.zip.part
echo '109f04cf8f124eb551d33c100e549730  ore2015_sample.zip.part' | md5sum -c -
mv ore2015_sample.zip.part ore2015_sample.zip
python3 - <<'PY'
from pathlib import Path
import zipfile,hashlib,json,os
root=Path.cwd()
with zipfile.ZipFile('ore2015_sample.zip') as z:
 for n in z.namelist():
  p=Path(n);assert not p.is_absolute() and '..' not in p.parts,n
 z.extractall('corpus')
files=sorted((root/'corpus/pool_sample/files').glob('*.owl'))
assert len(files)==1920,len(files)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
manifest={p.name:sha(p) for p in files}
(root/'corpus-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
for i in range(60):
 (root/'chunks'/f'{i:03d}.txt').write_text(''.join(p.stem+'\n' for p in files[i*32:(i+1)*32]))
km=Path('/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/v142-rc1/km.ibex')
assert sha(km)=='705cac1500018d18018ca4d5482a7451e836091b26648453824afa4b36d16fdb'
(root/'input-receipt.json').write_text(json.dumps(dict(harness_commit='7559c4543b270eb3a26cc88a6d4e837cffa0b84f',corpus_files=len(files),archive_sha256=sha(root/'ore2015_sample.zip'),manifest_sha256=sha(root/'corpus-sha256.json'),baseline_km_sha256=sha(km),slurm_job=os.environ['SLURM_JOB_ID']),indent=2)+'\n')
PY
cd source
CARGO_BUILD_JOBS=4 CARGO_TARGET_DIR="$root/target" cargo build --release --locked
sha256sum "$root/target/release/owl-reasoner-harness" > "$root/harness-binary.sha256"
touch "$root/STAGE-COMPLETE"
