"""Instrument selected timeout cases; never use these times for acceptance."""
import hashlib
import json
import os
from pathlib import Path
from measure_classification import measure

root = Path(__file__).resolve().parent
manifest = root / 'timeout-profile-inputs.json'
inventory_path = root / 'nominal-guard-candidate-artifact.json'
inputs = json.loads(manifest.read_text())['inputs']
row = inputs[int(os.environ['SLURM_ARRAY_TASK_ID'])]
inventory = json.loads(inventory_path.read_text())
os.environ.update(inventory['flags'])
os.environ.update(KM_TIMING='1', KM_BRIDGE_PROGRESS='1', KM_BRIDGE_PHASE_TIMING='1',
                  KM_HT_STATS='1', KM_CONFORMANCE_TIMING='1')
destination = root / ('timeout-profile-' + os.environ['SLURM_ARRAY_JOB_ID']) / row['ontology']
os.environ['KM_DUMP_TIN'] = str(destination / 'typed-input.json')
record = measure(inventory, 'km', row['path'], row['sha256'], destination,
                 timeout=60, memory_mib=20480)
receipt = {'diagnostic_only': True, 'input': row, 'flags': inventory['flags'],
           'status': record['status'], 'timeout_s': 60,
           'runner_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'manifest_sha256': hashlib.sha256(manifest.read_bytes()).hexdigest(),
           'inventory_sha256': hashlib.sha256(inventory_path.read_bytes()).hexdigest(),
           'record_sha256': hashlib.sha256((destination/'record.json').read_bytes()).hexdigest(),
           'scope': 'Instrumented phase trace only; any completed answer still requires independent verification.'}
(destination/'profile-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
if record['status'] == 'adapter_error':
    raise RuntimeError(record)
