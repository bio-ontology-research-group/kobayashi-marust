"""Report the full frozen panel and paired costs from source-bound audits.

Run on a Slurm worker with the measurement root, audit job, manifest, and run set.
Partial reports retain missing cases and never imply release readiness.
"""
import argparse
from collections import Counter
import itertools
import json
import math
from pathlib import Path
import statistics

from measure_classification import digest
from run_set import load


def paired_costs(pairs):
    """Ratios are right/left on the same cases; no imputation for failures."""
    result = {'cases': len(pairs), 'ratio_direction': 'right / left'}
    for field in ('wall_s', 'peak_bytes'):
        values = [(a.get(field), b.get(field)) for a, b in pairs]
        values = [(a, b) for a, b in values
                  if isinstance(a, (int, float)) and isinstance(b, (int, float))
                  and math.isfinite(a) and math.isfinite(b) and a > 0 and b > 0]
        result[field] = {'measured_pairs': len(values)}
        if values:
            result[field].update(left_median=statistics.median(a for a, _ in values),
                                 right_median=statistics.median(b for _, b in values),
                                 median_paired_ratio=statistics.median(b/a for a, b in values))
    return result


def measured_path(root, runs, baseline, ontology):
    if baseline == 'konclude':
        return root / ('classification-konclude-' + runs['classification_konclude']) / baseline / ontology
    job = runs['classification_km' if baseline == 'km' else 'classification']
    return root / ('classification-' + job) / baseline / ontology


def report(root, audit_job, manifest_path, runs):
    root = Path(root)
    manifest = json.loads(Path(manifest_path).read_text())['inputs']
    inventory = json.loads((root / runs['inventory']).read_text())['artifacts']
    baselines = sorted(row['id'] for row in inventory)
    assert len(baselines) == len(set(baselines)), 'duplicate baseline'
    artifacts = {row['id']: row for row in inventory}
    coverage = {b: Counter() for b in baselines}
    comparisons = {pair: Counter() for pair in itertools.combinations(baselines, 2)}
    costs = {pair: [] for pair in comparisons}
    issues, cases = [], []
    for index, source in enumerate(manifest):
        ontology = source['ontology']
        audit_path = root / ('classification-audit-' + audit_job) / str(index // 32) / ontology / 'audit.json'
        summary_path = audit_path.parent.parent / 'summary.json'
        case = {'ontology': ontology, 'input_admission': source['input_admission'],
                'source_sha256': source['sha256'], 'outcomes': {}}
        audit = None
        if audit_path.exists():
            audit = json.loads(audit_path.read_text())
            summary = json.loads(summary_path.read_text())
            assert summary['run_set'] == runs, 'audit run set differs'
            assert summary['manifest_sha256'] == digest(manifest_path), 'audit manifest differs'
            assert audit['source_sha256'] == source['sha256'], 'audit source differs'
            case['audit_status'] = audit['status']
            case['audit_sha256'] = digest(audit_path)
        else:
            case['audit_status'] = 'missing_audit'
        measured = {}
        for baseline in baselines:
            path = measured_path(root, runs, baseline, ontology)
            if not (path / 'record.json').exists():
                outcome = {'measurement_status': 'missing_measurement'}
            else:
                record = json.loads((path / 'record.json').read_text())
                assert record['source_sha256'] == source['sha256'], 'measurement source differs'
                assert record['artifact_sha256'] == artifacts[baseline]['sha256'], 'measurement artifact differs'
                outcome = {'measurement_status': record['status'], 'record': str(path / 'record.json')}
                if audit and baseline in audit.get('outcomes', {}):
                    audited = audit['outcomes'][baseline]
                    if 'measurement_receipt_sha256' in audited:
                        assert digest(path / 'record.json') == audited['measurement_receipt_sha256'], 'receipt changed after audit'
                    outcome['audit_status'] = audited['status']
                    if audited['status'] == 'canonicalized_requires_comparison':
                        assert record['timeout_s'] == 240 and record['memory_mib'] == 20480, 'resource limits differ'
                        assert record['cpu_threads'] == 1 and len(record['cpu_affinity']) == 1, 'CPU limits differ'
                        assert digest(path / 'taxonomy.raw') == record['files']['taxonomy.raw']['sha256'], 'taxonomy changed'
                        canonical = audit_path.parent / (baseline + '.validated.json')
                        assert digest(canonical) == audited['canonical_sha256'], 'canonical receipt changed'
                        measured[baseline] = record
                if record['status'] in ('running', 'preparing'):
                    issues.append({'ontology': ontology, 'baseline': baseline, 'status': 'measurement_active'})
            case['outcomes'][baseline] = outcome
            coverage[baseline][source['input_admission'] + ':' + outcome['measurement_status']] += 1
        if not audit or audit['status'] != 'audited_available_outputs':
            issues.append({'ontology': ontology, 'status': case['audit_status']})
        available = {(c['left'], c['right']): c for c in (audit or {}).get('comparisons', [])}
        for pair in comparisons:
            comparison = available.get(pair)
            if comparison is None:
                comparisons[pair]['comparison_unavailable'] += 1
                continue
            comparisons[pair][comparison['status']] += 1
            if comparison.get('agreement') is False or comparison.get('taxonomy_agreement') is False:
                issues.append({'ontology': ontology, 'pair': pair, 'status': comparison['status']})
            if comparison.get('agreement') is True and source['input_admission'] != 'invalid_input':
                assert all(b in measured for b in pair), 'agreement lacks bound measurements'
                costs[pair].append(tuple(measured[b] for b in pair))
        cases.append(case)
    return {'schema': 1, 'status': 'report_requires_review', 'run_set': runs,
            'audit_job': audit_job, 'manifest_sha256': digest(manifest_path),
            'expected_inputs': len(manifest), 'coverage': coverage, 'issues': issues,
            'pairwise': [{'left': pair[0], 'right': pair[1], 'outcomes': counts,
                          'costs_on_valid_fully_agreeing_cases': paired_costs(costs[pair])}
                         for pair, counts in comparisons.items()], 'cases': cases}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('root', type=Path)
    parser.add_argument('audit_job')
    parser.add_argument('manifest', type=Path)
    parser.add_argument('run_set')
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    result = report(args.root, args.audit_job, args.manifest, load(args.root, args.run_set))
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
