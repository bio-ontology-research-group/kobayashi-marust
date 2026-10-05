"""Coverage and paired generation costs for every frozen explanation query."""
import argparse
from collections import Counter
import csv
import itertools
import json
from pathlib import Path

from audit_justification import audit
from measure_classification import digest
from report_classification import paired_costs
from run_set import load


def measurement_path(root, runs, baseline, ontology, repetition, query):
    key = ('justifications_km' if baseline == 'km' else 'justifications_native' if baseline == 'rustdl'
           else 'justifications_external' if baseline in ('konclude', 'sequoia', 'more')
           else 'justifications_whelk' if baseline == 'whelk' else 'justifications_java')
    return root / ('java-justifications-' + runs[key]) / ontology / baseline / f'repetition-{repetition}' / query


def report(root, audit_job, runs):
    root = Path(root)
    selection = json.loads((root / 'workload-selection.json').read_text())['selected']
    inventory = {r['id']: r for r in json.loads((root / runs['inventory']).read_text())['artifacts']}
    baselines = sorted(inventory)
    coverage = {b: Counter() for b in baselines}
    eligibility = Counter()
    successes = {b: {} for b in baselines}
    sources, issues = [], []
    for source in selection:
        ontology = source['ontology']
        prepared = root / ('prepared-queries-' + runs['queries_preparation']) / ontology
        receipt_path = prepared / 'receipt.json'
        row = {'ontology': ontology, 'source_sha256': source['sha256'], 'cases': []}
        sources.append(row)
        if not receipt_path.exists():
            row['status'] = 'missing_preparation'
            eligibility[row['status']] += 1
            continue
        receipt = json.loads(receipt_path.read_text())
        assert receipt['source_sha256'] == source['sha256'], 'prepared source differs'
        row['preparation_receipt_sha256'] = digest(receipt_path)
        if receipt['status'] != 'prepared':
            row.update(status='query_preparation_failed', reason=receipt.get('error'))
            eligibility[row['status']] += 1
            continue
        query_file = prepared / 'queries/queries.tsv'
        assert digest(query_file) == receipt['files']['queries.tsv']['sha256'], 'queries changed'
        with query_file.open() as stream:
            queries = list(csv.DictReader(stream, delimiter='\t'))
        row.update(status='eligible_queries' if queries else 'no_eligible_inferred_queries', queries=len(queries))
        eligibility[row['status']] += 1
        audit_path = root / ('justification-audit-' + audit_job) / ontology / 'audit.json'
        audited = {}
        if audit_path.exists():
            evidence = json.loads(audit_path.read_text())
            assert evidence['run_set'] == runs, 'audit run set differs'
            assert evidence['source_sha256'] == source['sha256'], 'audit source differs'
            assert evidence['preparation_receipt_sha256'] == digest(receipt_path), 'preparation changed after audit'
            row['audit_sha256'] = digest(audit_path)
            for c in evidence['cases']:
                key = (c['baseline'], c['query'], c['repetition'])
                assert key not in audited, 'duplicate audited case'
                audited[key] = c
        for query in queries:
            for baseline in baselines:
                for repetition in range(3):
                    key = (baseline, query['query'], repetition)
                    case = dict(audited.get(key, {'status': 'missing_audit'}),
                                baseline=baseline, query=query['query'], repetition=repetition)
                    path = measurement_path(root, runs, baseline, ontology, repetition, query['query'])
                    if 'measurement_receipt_sha256' in case:
                        assert digest(path / 'record.json') == case['measurement_receipt_sha256'], 'measurement changed'
                    if case['status'] == 'verified_evidence_intact':
                        verifier = inventory['jfact' if baseline == 'hermit' else 'hermit']
                        checked = audit(path, inventory[baseline], verifier, source['sha256'],
                                        query['module_sha256'], [query['sub_iri'], query['super_iri']])
                        assert checked['status'] == 'verified_evidence_intact'
                        successes[baseline][(ontology, query['query'], repetition)] = {
                            'wall_s': checked['generation_wall_s'], 'peak_bytes': checked['generation_peak_bytes']}
                        case.update(checked)
                    coverage[baseline][case['status']] += 1
                    if case['status'] in ('missing_audit', 'evidence_validation_error', 'missing_measurement'):
                        issues.append({'ontology': ontology, **case})
                    row['cases'].append(case)
    pairs = []
    for left, right in itertools.combinations(baselines, 2):
        common = sorted(set(successes[left]) & set(successes[right]))
        pairs.append({'left': left, 'right': right,
                      'common_verified_generation_costs': paired_costs([(successes[left][k], successes[right][k]) for k in common]),
                      'common_cases': common})
    return {'schema': 1, 'status': 'report_requires_review', 'run_set': runs,
            'audit_job': audit_job, 'selected_ontologies': len(selection),
            'eligibility': eligibility, 'coverage_per_query_repetition': coverage,
            'pairwise': pairs, 'sources': sources, 'issues': issues,
            'selection_sha256': digest(root / 'workload-selection.json')}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('root', type=Path)
    parser.add_argument('audit_job')
    parser.add_argument('run_set')
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    result = report(args.root, args.audit_job, load(args.root, args.run_set))
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
