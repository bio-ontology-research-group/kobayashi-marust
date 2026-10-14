"""Paired 15687 phase diagnostics on pinned binaries; not release evidence."""
import hashlib
import json
import os
from pathlib import Path
from measure_classification import measure

root = Path(__file__).resolve().parent
manifest = root / 'full-candidate-inputs.json'
row, = [r for r in json.loads(manifest.read_text())['inputs']
        if r['ontology'] == 'ore_ont_15687']
output = root / ('15687-candidate-profile-' + os.environ['SLURM_JOB_ID'])
output.mkdir(exist_ok=False)
variants = ['data-source', 'work-budget', 'dense-data']
records = []
for repeat in range(2):
    # Reverse order on repetition to expose ordering effects within one node.
    for variant in (variants if repeat == 0 else list(reversed(variants))):
        inventory_path = root / (variant + '-candidate-artifact.json')
        inventory = json.loads(inventory_path.read_text())
        for key in list(os.environ):
            if key.startswith('KM_'):
                del os.environ[key]
        flags = dict(inventory['flags'], KM_TIMING='1', KM_BRIDGE_PROGRESS='1',
                     KM_BRIDGE_PHASE_TIMING='1', KM_HT_STATS='1', KM_CONFORMANCE_TIMING='1')
        os.environ.update(flags)
        destination = output / (str(repeat) + '-' + variant)
        record = measure(inventory, 'km', row['path'], row['sha256'], destination,
                         timeout=240, memory_mib=20480)
        receipt = dict(variant=variant, repeat=repeat, flags=flags,
                       status=record['status'], wall_s=record.get('wall_s'),
                       peak_bytes=record.get('peak_bytes'),
                       inventory_sha256=hashlib.sha256(inventory_path.read_bytes()).hexdigest(),
                       record_sha256=hashlib.sha256((destination/'record.json').read_bytes()).hexdigest())
        records.append(receipt)
        result = dict(diagnostic_only=True, input=row, timeout_s=240, memory_mib=20480,
                      runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                      manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),
                      records=records, complete=len(records)==6,
                      scope='Instrumented repeated same-node comparisons. Preserve the full-sweep timeout; successful outputs require independent semantic audit.')
        temp = output / 'summary.part'
        temp.write_text(json.dumps(result, indent=2)+'\n')
        temp.replace(output / 'summary.json')
        print(json.dumps(receipt), flush=True)
        if record['status'] == 'adapter_error':
            raise RuntimeError(record)
