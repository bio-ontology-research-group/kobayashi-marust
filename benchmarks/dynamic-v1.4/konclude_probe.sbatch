#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:05:00
set -euo pipefail
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
cd /ibex/scratch/hohndor/km/dynamic-benchmark-20260917
mkdir -p konclude-probe
python3 - <<'PY'
from pathlib import Path
p=Path('inputs/chains/state-000.ofn').resolve().as_uri()
Path('konclude-probe/request.xml').write_text(f'''<RequestMessage xmlns="http://www.owllink.org/owllink-xml#" xmlns:owl="http://www.w3.org/2002/07/owl#"><CreateKB kb="urn:km:probe"/><LoadOntologies kb="urn:km:probe"><OntologyIRI IRI="{p}"/></LoadOntologies><IsClassSatisfiable kb="urn:km:probe"><owl:Class IRI="http://www.w3.org/2002/07/owl#Thing"/></IsClassSatisfiable><GetSubClassHierarchy kb="urn:km:probe"/></RequestMessage>''')
PY
/ibex/scratch/hohndor/km/Konclude-official owllinkfile -w 1 -i konclude-probe/request.xml -o konclude-probe/response.xml
