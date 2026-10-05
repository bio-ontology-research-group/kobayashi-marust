"""Run the frozen real-ontology justification panel for Java and native baselines."""
import csv
import json
import os
from pathlib import Path
import subprocess
import sys

from measure_justification_java import measure, digest

root, task, job = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
preparation_job = sys.argv[4]
selection = json.loads((root / 'workload-selection.json').read_text())['selected']
baselines = sys.argv[5].split(',') if len(sys.argv) > 5 else ['hermit', 'jfact', 'openllet', 'elk', 'whelk']
inventory_name = sys.argv[6] if len(sys.argv) > 6 else 'artifact-inventory-53198415.json'
source = selection[task // len(baselines)]
baseline = baselines[task % len(baselines)]
inventory = {r['id']: r for r in json.loads((root / inventory_name).read_text())['artifacts']}
generator, verifier = inventory[baseline], inventory['jfact' if baseline == 'hermit' else 'hermit']
out = root / ('java-justifications-' + job) / source['ontology'] / baseline
out.mkdir(parents=True, exist_ok=False)
summary = {'ontology': source['ontology'], 'generator': baseline, 'verifier': verifier['id'],
           'source_sha256': source['sha256'], 'status': 'preparing', 'cases': [],
           'runner_sha256': digest(__file__), 'slurm_job_id': os.getenv('SLURM_JOB_ID')}
def publish():
    temporary = out / 'summary.json.part'
    temporary.write_text(json.dumps(summary, indent=2) + '\n')
    temporary.replace(out / 'summary.json')
publish()
try:
    prepared = root / ('prepared-queries-' + preparation_job) / source['ontology']
    receipt = json.loads((prepared / 'receipt.json').read_text())
    summary['query_preparation_receipt_sha256'] = digest(prepared / 'receipt.json')
    if receipt['status'] != 'prepared':
        summary.update(status='query_preparation_failed', preparation_error=receipt.get('error'))
    else:
        assert receipt['source_sha256'] == source['sha256'], 'query source hash mismatch'
        query_file = prepared / 'queries/queries.tsv'
        assert digest(query_file) == receipt['files']['queries.tsv']['sha256'], 'query manifest changed'
        with query_file.open() as stream:
            queries = list(csv.DictReader(stream, delimiter='\t'))
        summary['query_count'] = len(queries)
        if not queries:
            summary['status'] = 'no_eligible_inferred_queries'
        else:
            sources = Path(__file__).parent
            summary['worker_sources'] = {name: digest(sources / name) for name in ['EntailmentExplanation.java', 'VerifyJustification.java']}
            for label, row, filename in [('generator', generator, 'EntailmentExplanation.java'),
                                         ('verifier', verifier, 'VerifyJustification.java')]:
                if label == 'generator' and baseline in ['km', 'rustdl']:
                    continue
                assert digest(row['path']) == row['sha256'], 'runtime hash mismatch'
                classes = out / label
                classes.mkdir()
                command = ['javac', '--release', '11', '-cp', row['path'], '-d', str(classes), str(sources / filename)]
                with (out / (label + '.compile.stdout')).open('wb') as stdout, (out / (label + '.compile.stderr')).open('wb') as stderr:
                    subprocess.run(command, stdout=stdout, stderr=stderr, check=True, timeout=60)
            summary['status'] = 'running'
            for repetition in range(3):
                for query in queries:
                    module = prepared / 'queries' / (query['query'] + '.ofn')
                    assert query['module_sha256'] == receipt['files'][module.name]['sha256'], 'module binding mismatch'
                    result = measure(generator, verifier, None if baseline in ['km', 'rustdl'] else out / 'generator', out / 'verifier',
                                     source['path'], source['sha256'], module, query['module_sha256'],
                                     query['sub_iri'], query['super_iri'],
                                     out / f'repetition-{repetition}' / query['query'])
                    summary['cases'].append({'repetition': repetition, 'query': query['query'],
                                             'status': result['status'], 'error': result.get('error')})
                    publish()
            summary['status'] = 'measurement_complete'
except Exception as error:
    summary.update(status='preparation_or_adapter_error', error=str(error))
publish()
print(json.dumps(summary))
