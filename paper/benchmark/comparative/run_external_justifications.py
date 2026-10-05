"""Run the frozen real-ontology justification panel for Java and native baselines."""
import csv
import json
import os
from pathlib import Path
import subprocess
import sys

from measure_justification_java import measure, digest
from measure_classification import measure as classify
from taxonomy import parse

root, task, job = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
preparation_job = sys.argv[4]
selection = json.loads((root / 'workload-selection.json').read_text())['selected']
baselines = ['konclude', 'sequoia', 'more']
inventory_name = 'artifact-inventory-53198415.json'
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
            filenames = ['ExportExplanationAxioms.java', 'SourceSignature.java', 'ConvertSyntax.java', 'VerifyJustification.java']
            summary['worker_sources'] = {name: digest(sources / name) for name in filenames}
            assert digest(verifier['path']) == verifier['sha256'], 'verifier runtime hash mismatch'
            classes = out / 'classes'; classes.mkdir()
            command = ['javac', '--release', '11', '-cp', verifier['path'], '-d', str(classes)] + [str(sources / name) for name in filenames]
            with (out / 'compile.stdout').open('wb') as stdout, (out / 'compile.stderr').open('wb') as stderr:
                subprocess.run(command, stdout=stdout, stderr=stderr, check=True, timeout=60)
            certificates = {}
            preparation_failures = {}
            if baseline == 'more':
                for query in queries:
                    module = prepared / 'queries' / (query['query'] + '.ofn')
                    reference_dir = out / 'module-consistency' / query['query']
                    measured = classify({'artifacts': list(inventory.values())}, 'hermit', module,
                                        query['module_sha256'], reference_dir)
                    if measured['status'] != 'executed_unvalidated':
                        preparation_failures[query['query']] = measured['status']
                        continue
                    taxonomy = reference_dir / 'taxonomy.raw'
                    checked = parse(taxonomy.read_text(), 'owlapi-tsv')
                    if checked['consistent'] is not True:
                        preparation_failures[query['query']] = 'module_consistency_not_established'
                        continue
                    certificates[query['query']] = {'module_sha256': query['module_sha256'],
                        'verifier': 'hermit', 'taxonomy': str(taxonomy), 'taxonomy_sha256': digest(taxonomy),
                        'format': 'owlapi-tsv', 'artifact_sha256': verifier['sha256'],
                        'measurement_receipt_sha256': digest(reference_dir / 'record.json')}
            summary['consistency_preparation_failures'] = preparation_failures
            summary['status'] = 'running'
            for repetition in range(3):
                for query in queries:
                    module = prepared / 'queries' / (query['query'] + '.ofn')
                    assert query['module_sha256'] == receipt['files'][module.name]['sha256'], 'module binding mismatch'
                    if query['query'] in preparation_failures:
                        summary['cases'].append({'repetition': repetition, 'query': query['query'], 'status': 'consistency_preparation_failed', 'error': preparation_failures[query['query']]})
                        publish()
                        continue
                    result = measure(generator, verifier, classes, classes,
                                     source['path'], source['sha256'], module, query['module_sha256'],
                                     query['sub_iri'], query['super_iri'],
                                     out / f'repetition-{repetition}' / query['query'],
                                     consistency_certificate=certificates.get(query['query']))
                    summary['cases'].append({'repetition': repetition, 'query': query['query'],
                                             'status': result['status'], 'error': result.get('error')})
                    publish()
            summary['status'] = 'measurement_complete'
except Exception as error:
    summary.update(status='preparation_or_adapter_error', error=str(error))
publish()
print(json.dumps(summary))
