"""Paired source-update results, retaining preparation and reasoning failures."""
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path

from compare_taxonomies import compare
from measure_classification import digest
from report_classification import paired_costs
from run_set import load


def measurement_path(root, runs, baseline, mode, ontology, repetition, revision):
    repeat = f'repetition-{repetition}'
    if baseline == 'konclude':
        if mode == 'retained':
            return root / ('konclude-retained-' + runs['retained_konclude']) / ontology / repeat
        return root / ('konclude-updates-' + runs['updates_konclude']) / ontology / repeat / f'{revision:03}'
    if baseline in ('rustdl', 'more', 'sequoia'):
        return root / ('native-updates-' + runs['updates_native']) / ontology / baseline / repeat / f'{revision:03}'
    job = ('km-updates-' + runs['updates_km']) if baseline == 'km' else (
        'java-updates-' + runs['updates_whelk' if baseline == 'whelk' else 'updates_java'])
    path = root / job / ontology / baseline / repeat / mode
    return path if mode == 'retained' else path / f'{revision:03}'


def report(root, audit_job, runs):
    root = Path(root)
    selection = json.loads((root / 'workload-selection.json').read_text())['selected']
    inventory = {r['id']: r for r in json.loads((root / runs['inventory']).read_text())['artifacts']}
    methods = [(b, m) for b in sorted(inventory)
               for m in (['cold'] if b in ('rustdl', 'more', 'sequoia') else ['cold', 'retained'])]
    names = ['-'.join(m) for m in methods]
    coverage = {name: Counter() for name in names}
    pairs = list(itertools.combinations(names, 2))
    counts = {(phase, pair): Counter() for phase in ('initialization', 'updates') for pair in pairs}
    costs = {key: [] for key in counts}
    sources, issues, reuse = [], [], []
    for source in selection:
        ontology = source['ontology']
        directory = root / ('update-audit-' + audit_job) / ontology
        preparation = root / ('prepared-updates-' + runs['updates_preparation']) / ontology / 'receipt.json'
        row = {'ontology': ontology, 'source_sha256': source['sha256'], 'revisions': []}
        sources.append(row)
        prepared = json.loads(preparation.read_text()) if preparation.exists() else {'status': 'missing_preparation'}
        if preparation.exists():
            assert prepared['source_sha256'] == source['sha256'], 'prepared source differs'
        row['preparation_status'] = prepared['status']
        if (directory / 'summary.json').exists():
            summary = json.loads((directory / 'summary.json').read_text())
            assert summary['run_set'] == runs, 'audit run set differs'
            assert summary['source_sha256'] == source['sha256'], 'audit source differs'
            if 'preparation_receipt_sha256' in summary:
                assert digest(preparation) == summary['preparation_receipt_sha256'], 'preparation changed'
        for revision in range(5):
            phase = 'initialization' if revision == 0 else 'updates'
            audit_path = directory / f'{revision:03}' / 'audit.json'
            evidence = json.loads(audit_path.read_text()) if audit_path.exists() else {}
            status = evidence.get('status', 'missing_audit' if prepared['status'] == 'prepared' else 'preparation_failed')
            row['revisions'].append({'revision': revision, 'status': status})
            if status != 'audited_available_outputs':
                issues.append({'ontology': ontology, 'revision': revision, 'status': status})
            for repetition in range(3):
                canonical, measurements = {}, {}
                for baseline, mode in methods:
                    name = baseline + '-' + mode
                    key = name + '-' + str(repetition)
                    outcome = evidence.get('outcomes', {}).get(key, {'status': status})
                    coverage[name][outcome['status']] += 1
                    if outcome['status'] != 'canonicalized_requires_comparison':
                        continue
                    path = measurement_path(root, runs, baseline, mode, ontology, repetition, revision)
                    record = json.loads((path / 'record.json').read_text())
                    assert digest(path / 'record.json') == outcome['measurement_receipt_sha256'], 'measurement changed'
                    assert record['artifact_sha256'] == inventory[baseline]['sha256'], 'artifact differs'
                    assert record['memory_mib'] == 20480 and len(record['cpu_affinity']) == 1, 'resource limits differ'
                    assert record['timeout_s' if mode == 'cold' else 'timeout_per_revision_s'] == 240, 'deadline differs'
                    stage = record if mode == 'cold' else record['revisions'][revision]
                    if mode == 'cold':
                        raw = path / 'taxonomy.raw'
                    elif baseline == 'km':
                        raw = path / f'{revision:03}.response.json'
                    elif baseline == 'konclude':
                        raw = path / f'{revision:03}.taxonomy.json'
                    else:
                        raw = path / 'session' / f'{revision:03}.taxonomy.tsv'
                    assert digest(raw) == outcome['raw_sha256'], 'raw output changed'
                    canonical_path = audit_path.parent / (key + '.validated.json')
                    assert digest(canonical_path) == outcome['canonical_sha256'], 'canonical receipt changed'
                    validated = json.loads(canonical_path.read_text())
                    assert validated['source_sha256'] == prepared['files'][f'{revision:03}.ofn'], 'revision differs'
                    canonical[name], measurements[name] = validated, outcome
                    if mode == 'retained':
                        reuse.append({'ontology': ontology, 'revision': revision, 'repetition': repetition,
                                      'baseline': baseline, 'route': stage.get('route'),
                                      'retained_backend': stage.get('retained_backend'),
                                      'reuse_receipt': stage.get('reuse_receipt'),
                                      'internal_reuse': 'see_receipt' if stage.get('reuse_receipt') else 'unknown'})
                for pair in pairs:
                    bucket = (phase, pair)
                    if not all(name in canonical for name in pair):
                        counts[bucket]['comparison_unavailable'] += 1
                        continue
                    comparison = compare(*(canonical[name] for name in pair))
                    counts[bucket][comparison['status']] += 1
                    if comparison.get('agreement') is True:
                        costs[bucket].append(tuple(measurements[name] for name in pair))
                    if comparison.get('agreement') is False or comparison.get('taxonomy_agreement') is False:
                        issues.append({'ontology': ontology, 'revision': revision, 'repetition': repetition,
                                       'pair': pair, 'status': comparison['status']})
    return {'schema': 1, 'status': 'report_requires_review', 'audit_job': audit_job, 'run_set': runs,
            'selected_ontologies': len(selection), 'revisions_per_ontology': 5, 'repetitions': 3,
            'coverage_per_revision_repetition': coverage, 'sources': sources, 'issues': issues,
            'selection_sha256': digest(root / 'workload-selection.json'), 'retained_reuse': reuse,
            'pairwise': [{'phase': phase, 'left': pair[0], 'right': pair[1], 'outcomes': counter,
                          'costs_on_fully_agreeing_cases': paired_costs(costs[(phase, pair)])}
                         for (phase, pair), counter in counts.items()]}


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
