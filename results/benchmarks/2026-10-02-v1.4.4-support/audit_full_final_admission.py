#!/usr/bin/env python3
"""Audit completed candidate outputs against recorded hashes and v1.4.3."""
import argparse
import collections
import hashlib
import json
from pathlib import Path
from recovery_reference_audit import check_reference
from conformance_execution_audit import inspect_execution

parser = argparse.ArgumentParser()
parser.add_argument('--candidate-root', type=Path, required=True)
parser.add_argument('--baseline-root', type=Path, required=True)
parser.add_argument('--job', required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--recovery-references', type=Path)
parser.add_argument('--corpus-root', type=Path)
args = parser.parse_args()
args.recovery_references = args.recovery_references or args.candidate_root / 'main-lazy-recovery-references.json'
args.corpus_root = args.corpus_root or args.baseline_root.parent / 'corpus/pool_sample/files'
recovery_references = json.loads(args.recovery_references.read_text())

def read_cases(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    return [row for row in rows if row.get('kind') == 'case']

def verified_bytes(path, row):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != row['out_sha256']:
        raise RuntimeError(f'Output hash differs from harness record: {path}')
    return raw

candidate = {}
baseline = {}
for chunk in range(60):
    current = args.candidate_root / f'full-v144-final-admission-{args.job}_{chunk}'
    old = args.baseline_root / f'{chunk:03}'
    if not (current / 'COMPLETE').is_file():
        raise RuntimeError(f'Incomplete chunk: {current}')
    for table, directory in [(candidate, current), (baseline, old)]:
        for row in read_cases(directory / 'results.jsonl'):
            ont = row['ont']
            if ont in table:
                raise RuntimeError(f'Duplicate ontology: {ont}')
            table[ont] = (row, directory / 'output' / f'{ont}.json')
if len(candidate) != 1920 or candidate.keys() != baseline.keys():
    raise RuntimeError('Candidate and baseline must cover the same 1920 ontologies')

results = []
for ont, (row, path) in sorted(candidate.items()):
    old, old_path = baseline[ont]
    result = dict(ont=ont, outcome=row['outcome'], baseline_outcome=old['outcome'])
    result.update(inspect_execution(path, ont, row['outcome']))
    if row['outcome'] == 'ok':
        raw = verified_bytes(path, row)
        current = json.loads(raw)
        result.update(consistent=current['consistent'], dropped=current['dropped'])
        if ont in recovery_references:
            result.update(check_reference(recovery_references[ont],
                (args.corpus_root / f'{ont}.owl').read_bytes(), raw))
        if old['outcome'] == 'ok':
            old_raw = verified_bytes(old_path, old)
            result['byte_identical'] = raw == old_raw
            if raw != old_raw:
                previous = json.loads(old_raw)
                observed = {tuple(pair) for pair in current['subsumptions']}
                expected = {tuple(pair) for pair in previous['subsumptions']}
                result.update(
                    baseline_dropped=previous['dropped'],
                    consistency_equal=current['consistent'] == previous['consistent'],
                    unsatisfiable_equal=set(current['unsatisfiable']) == set(previous['unsatisfiable']),
                    missing_relations=len(expected - observed),
                    extra_relations=len(observed - expected),
                    missing_sample=sorted(expected - observed)[:10],
                    extra_sample=sorted(observed - expected)[:10],
                )
    results.append(result)
summary = dict(
    job=args.job,
    cases=len(results),
    outcomes=dict(collections.Counter(row['outcome'] for row in results)),
    reported_outcomes=dict(collections.Counter(row['reported_outcome'] for row in results)),
    missing_execution_records=sum(not row['execution_record_present'] for row in results),
    successful_outputs_with_dropped=sum(row.get('dropped', 0) != 0 for row in results),
    byte_identical_successes=sum(row.get('byte_identical', False) for row in results),
    independent_reference_matches=sum(row.get('independent_reference_equal') is True for row in results),
    independent_reference_mismatches=sum(row.get('independent_reference_equal') is False for row in results),
    recovery_cases_not_completed=[row['ont'] for row in results
        if row['ont'] in recovery_references and row['outcome'] != 'ok'],
    semantic_disagreements=sum(
        row.get('consistency_equal') is False or row.get('unsatisfiable_equal') is False
        or row.get('missing_relations', 0) > 0 or row.get('extra_relations', 0) > 0
        for row in results),
)
args.output.write_text(json.dumps(dict(summary=summary, results=results), indent=2) + '\n')
print(json.dumps(summary, indent=2))
