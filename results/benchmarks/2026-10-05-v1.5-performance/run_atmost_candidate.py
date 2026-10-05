"""Audit the dependency repair on the existing diagnostic selection, not release acceptance."""
import json
import os
from pathlib import Path

from canonicalize import canonicalize
from compare_taxonomies import compare
from measure_classification import digest, measure


root = Path(__file__).resolve().parent
selection = json.loads((root / 'paired-selection.json').read_text())
row = selection['inputs'][int(os.environ['SLURM_ARRAY_TASK_ID'])]
inventory = json.loads((root / 'atmost-candidate-artifact.json').read_text())
binding = json.loads((root / 'audit-references.json').read_text())[row['ontology']]
reference = Path(binding['directory'])
assert digest(reference / 'audit.json') == binding['audit_sha256']
reference_audit = json.loads((reference / 'audit.json').read_text())
assert reference_audit['source_sha256'] == row['sha256']
os.environ['KM_HT_DDB'] = '1'
destination = root / ('atmost-candidate-' + os.environ['SLURM_ARRAY_JOB_ID']) / row['ontology']
destination.mkdir(parents=True, exist_ok=False)
outcomes = []
for repetition in range(selection['repetitions']):
    output = destination / str(repetition)
    record = measure(inventory, 'km', row['path'], row['sha256'], output,
                     timeout=selection['timeout_s'], memory_mib=selection['memory_mib'])
    result = dict(repetition=repetition, status=record['status'],
                  wall_s=record.get('wall_s'), environment={'KM_HT_DDB': '1'},
                  comparisons={}, diagnostic_only=True)
    if record['status'] == 'executed_unvalidated':
        canonicalize(output / 'taxonomy.raw', 'km-json', reference / 'signature.tsv',
                     output / 'canonical', root / 'full_iri_fingerprint.py')
        answer = json.loads((output / 'canonical.validated.json').read_text())
        for baseline in ['konclude', 'hermit', 'openllet', 'jfact']:
            prior = reference_audit['outcomes'].get(baseline, {})
            if prior.get('status') != 'canonicalized_requires_comparison':
                continue
            path = reference / (baseline + '.validated.json')
            assert digest(path) == prior['canonical_sha256']
            result['comparisons'][baseline] = compare(answer, json.loads(path.read_text()))
        result['verified_solved'] = any(x.get('agreement') is True
                                       for x in result['comparisons'].values())
    outcomes.append(result)
    (destination / 'summary.json').write_text(json.dumps(dict(
        ontology=row['ontology'], source_sha256=row['sha256'], outcomes=outcomes,
        inventory_sha256=digest(root / 'atmost-candidate-artifact.json'),
        runner_sha256=digest(__file__)), indent=2) + '\n')
    if record['status'] == 'adapter_error':
        raise RuntimeError(record)
(destination / 'COMPLETE').touch()
