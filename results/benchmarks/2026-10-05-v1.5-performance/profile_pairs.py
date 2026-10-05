"""Separate 60-second phase diagnostics; never use these as benchmark timings."""
import json
import os
from pathlib import Path

from measure_classification import measure


root = Path(__file__).resolve().parent
row = json.loads((root / 'paired-selection.json').read_text())['inputs'][int(os.environ['SLURM_ARRAY_TASK_ID'])]
inventories = json.loads((root / 'paired-artifacts.json').read_text())
os.environ.update(KM_TIMING='1', KM_BRIDGE_PROGRESS='1', KM_BRIDGE_PHASE_TIMING='1')
for version in ['v144', 'v145']:
    destination = root / ('profiles-' + os.environ['SLURM_ARRAY_JOB_ID']) / row['ontology'] / version
    record = measure(inventories[version], 'km', row['path'], row['sha256'], destination,
                     timeout=60, memory_mib=20480)
    if record['status'] == 'adapter_error':
        raise RuntimeError(record)
