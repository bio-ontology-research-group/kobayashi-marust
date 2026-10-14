"""Separate 60-second phase diagnostics; never use these as benchmark timings."""
import json
import os
from pathlib import Path

from measure_classification import measure


root = Path(__file__).resolve().parent
row = json.loads((root / 'paired-selection.json').read_text())['inputs'][int(os.environ['SLURM_ARRAY_TASK_ID'])]
inventories = json.loads((root / 'paired-artifacts.json').read_text())
os.environ.update(KM_TIMING='1', KM_BRIDGE_PROGRESS='1', KM_BRIDGE_PHASE_TIMING='1', KM_HT_STATS='1', KM_HT_DDB='1', KM_HT_NO_SEMB='1')
for version in ['v145']:
    destination = root / ('profiles-' + os.environ['SLURM_ARRAY_JOB_ID']) / row['ontology'] / version
    os.environ['KM_DUMP_TIN'] = str(root / ('tin-' + os.environ['SLURM_ARRAY_JOB_ID'] + '-' + row['ontology'] + '-' + version + '.json'))
    record = measure(inventories[version], 'km', row['path'], row['sha256'], destination,
                     timeout=60, memory_mib=20480)
    if record['status'] == 'adapter_error':
        raise RuntimeError(record)
