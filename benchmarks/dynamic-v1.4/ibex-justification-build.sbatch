#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --time=00:10:00
#SBATCH --job-name=km-justification-build
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
mkdir -p justification-main/classes
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes
javac -cp "$runtime/classifier-hermit.jar" -d justification-main/classes DynamicBenchmark.java JustificationBenchmark.java JustificationPanel.java JustificationLibrary.java
python3 - <<'PY'
from pathlib import Path
import hashlib,json
root=Path.cwd().resolve()
paths=[root/n for n in ['DynamicBenchmark.java','JustificationBenchmark.java','JustificationPanel.java','JustificationLibrary.java','justification_run.py','justification_tasks.py','konclude_oracle.py','konclude_incremental.py','ibex-justification-main.sbatch']]
if (root/'justification-panel-selection.json').exists():paths.append(root/'justification-panel-selection.json')
paths+=list((root/'justification-main/classes').rglob('*.class'))
paths+=list(Path('/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes').glob('classifier-*.jar'))
paths+=[Path('/ibex/scratch/hohndor/km/v140-release-final-20260916/km.ibex'),Path('/home/hohndor/bench/reasoners/Konclude-v0.7.0-1138-Linux-x64-GCC-Static-Qt5.12.10/Binaries/Konclude')]
manifest={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
if manifest[str(paths[-2])]!='ddc30d2f9013b371b5c4ec19c0623c91ecc1b2dbdc172ded9002fd238903d09a':raise ValueError('KM baseline hash differs')
(root/'justification-main/driver-manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
PY
panel_args=()
if [[ -f justification-panel-selection.json ]]; then panel_args=(--panel justification-panel-selection.json); fi
python3 justification_tasks.py "$DYNAMIC_ROOT" "${panel_args[@]}"
echo JUSTIFICATION_BUILD_COMPLETE
