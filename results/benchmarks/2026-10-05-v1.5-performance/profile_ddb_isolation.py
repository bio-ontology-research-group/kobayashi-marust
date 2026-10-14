"""Isolate DDB failure on 2901; diagnostic flags are never production defaults."""
import json
import os
from pathlib import Path
from measure_classification import measure
root = Path(__file__).resolve().parent
row = json.loads((root / 'paired-selection.json').read_text())['inputs'][2]
assert row['ontology'] == 'ore_ont_2901'
inventory = json.loads((root / 'paired-artifacts.json').read_text())['v145']
variants = [('no_skip', 'KM_HT_DDB_NO_SKIP'), ('no_cache_read', 'KM_HT_NO_SAT_CACHE_READING'), ('no_cached_absorption', 'KM_HT_NO_SAT_CACHED_ABSORPTION')]
name, flag = variants[int(os.environ['SLURM_ARRAY_TASK_ID'])]
os.environ.update(KM_TIMING='1', KM_BRIDGE_PROGRESS='1', KM_BRIDGE_PHASE_TIMING='1', KM_HT_STATS='1', KM_HT_DDB='1', KM_BRIDGE_DUMP_CLASH='1')
os.environ[flag] = '1'
destination = root / ('ddb-isolation-' + os.environ['SLURM_ARRAY_JOB_ID']) / name
record = measure(inventory, 'km', row['path'], row['sha256'], destination, timeout=60, memory_mib=20480)
(destination / 'diagnostic-options.json').write_text(json.dumps({'scope':'diagnostic only','options':{k:v for k,v in os.environ.items() if k.startswith('KM_')}} ,indent=2)+'\n')
if record['status'] == 'adapter_error':
    raise RuntimeError(record)
