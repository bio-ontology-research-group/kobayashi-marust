"""Matched release-binary diagnostic, using the frozen classification runner."""
import json
import os
from pathlib import Path
import sys

from measure_classification import digest, measure


def main():
    root = Path(__file__).resolve().parent
    selection = json.loads((root / 'paired-selection.json').read_text())
    task = int(os.environ['SLURM_ARRAY_TASK_ID'])
    row = selection['inputs'][task]
    inventories = json.loads((root / 'paired-artifacts.json').read_text())
    destination = root / ('paired-' + os.environ['SLURM_ARRAY_JOB_ID']) / row['ontology']
    destination.mkdir(parents=True, exist_ok=False)
    receipts = []
    for repetition in range(selection['repetitions']):
        versions = ['v144', 'v145']
        if (task + repetition) % 2:
            versions.reverse()
        for version in versions:
            record = measure(inventories[version], 'km', row['path'], row['sha256'],
                             destination / version / str(repetition),
                             timeout=selection['timeout_s'], memory_mib=selection['memory_mib'])
            receipts.append(dict(version=version, repetition=repetition,
                                 status=record['status'], wall_s=record.get('wall_s'),
                                 peak_bytes=record.get('peak_bytes')))
            summary = dict(ontology=row['ontology'], group=row['group'],
                           selection_sha256=digest(root / 'paired-selection.json'),
                           inventory_sha256=digest(root / 'paired-artifacts.json'),
                           runner_sha256=digest(__file__), outcomes=receipts,
                           semantic_validation='pending')
            temporary = destination / 'summary.json.part'
            temporary.write_text(json.dumps(summary, indent=2) + '\n')
            temporary.replace(destination / 'summary.json')
            if record['status'] == 'adapter_error':
                raise RuntimeError(record)
    (destination / 'COMPLETE').touch()


if __name__ == '__main__':
    main()
