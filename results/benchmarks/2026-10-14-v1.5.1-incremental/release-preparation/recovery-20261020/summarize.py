#!/usr/bin/env python3
"""Summarize the frozen 80-case panel without dropping failed/missing cases.

Usage: summarize.py RECORD_ROOT INPUT_PLAN OUTPUT_JSON
RECORD_ROOT contains cli/task-NNN-ID and owlapi/task-NNN directories.
Recovery files are overlaid only for the explicitly storage-failed task indices.
All medians use five repetitions. Init is separate from the eight update cells.
"""
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys
from collections import Counter

ARMS = ('candidate_retained', 'candidate_fresh', 'released_baseline_retained', 'released_baseline_fresh')
CANDIDATE = '5ee715d66e391e561e188c735a8fa6a0aaabc4383e7d8bd243b52495b2cac3a8'
BASELINE = '1dbc0dd92170abcd70e948fa2dc2d9d13d5c72076bcff9ad7a664921188e5900'

def read(p):
    return json.loads(p.read_text()) if p.exists() else None

def valid(v):
    return isinstance(v, (int, float)) and not isinstance(v, bool) and math.isfinite(v) and v > 0

def ratio(a, b):
    if len(a) != 5 or len(b) != 5 or not all(valid(x) for x in a + b):
        return None
    pairs = [x / y for x, y in zip(a, b)]
    return {'paired_ratios': pairs, 'median_ratio': statistics.median(pairs)}

def times(values):
    return {arm: {'seconds': values.get(arm, []), 'median_s': statistics.median(values[arm])
                 if len(values.get(arm, [])) == 5 and all(valid(x) for x in values[arm]) else None}
            for arm in ARMS}

def comparisons(values):
    return {arm: ratio(values.get('candidate_retained', []), values.get(arm, [])) for arm in ARMS[1:]}

def semantic_check(audits):
    checked = 0
    missing = []
    differences = []
    for rep in range(5):
        for rev in range(9):
            arms = audits.get((rep, rev), {})
            ids = [arms.get(a) for a in ARMS]
            if any(not x or not x.get('canonical_sha256') for x in ids):
                missing.append([rep, rev])
                continue
            identities = [(x['canonical_sha256'], x['consistent']) for x in ids]
            checked += 1
            if len(set(identities)) != 1:
                differences.append({'repetition': rep, 'revision': rev, 'identities': dict(zip(ARMS, identities))})
    return {'four_arm_revisions_checked': checked, 'missing_four_arm_revision_checks': missing, 'differences': differences}

def summarize_case(root, path, fixture):
    idx, ont = fixture['index'], fixture['id']
    d = root / path / (f'task-{idx:03d}-{ont}' if path == 'cli' else f'task-{idx:03d}')
    p = read(d / ('four-arm-panel/panel.json' if path == 'cli' else 'panel/panel.json'))
    result = {'index': idx, 'ontology': ont, 'status': 'missing_panel', 'cells': [], 'attempt_statuses': {}}
    if p is None:
        return result
    result['panel_sha256'] = hashlib.sha256((d / ('four-arm-panel/panel.json' if path == 'cli' else 'panel/panel.json')).read_bytes()).hexdigest()
    result['panel_status'] = p['status']
    attempts = p.get('attempts', [])
    statuses = Counter()
    binding_errors = []
    audits = {}
    for a in attempts:
        expected = CANDIDATE if a['arm'].startswith('candidate') else BASELINE
        m = a.get('measurement', {})
        actual = a.get('binary_sha256') if path == 'cli' else m.get('binding', {}).get('binary_sha256')
        if actual != expected:
            binding_errors.append({'arm': a['arm'], 'rep': a['repetition'], 'actual': actual})
        statuses[(a['arm'], a.get('status', m.get('status', 'unknown')))] += 1
        if path == 'owlapi':
            for audit in a.get('semantic_audit', []):
                audits.setdefault((a['repetition'], audit['revision']), {})[a['arm']] = audit.get('semantic_identity')
    result['attempt_statuses'] = {f'{a}:{s}': n for (a, s), n in sorted(statuses.items())}
    result['binding_errors'] = binding_errors
    result['attempt_count'] = len(attempts)
    result['cleanup_verified'] = len(attempts) == 20 and all(a.get('cleanup_proven_empty') is True for a in attempts)
    if path == 'cli':
        summary = read(d / 'four-arm-panel' / ont / 'timing-summary.json')
        for audit_file in sorted((d / 'four-arm-panel' / ont).glob('semantic-audit-repetition-*.json')):
            audit = read(audit_file)
            for rv in audit['revisions']:
                audits[(audit['repetition'], rv['revision'])] = {a: x.get('semantic_identity') for a, x in rv['arms'].items()}
        revisions = summary.get('per_valid_revision', []) if summary else []
        whole = summary.get('whole_session', {}) if summary else {}
        sequence = {a: whole.get(a, {}).get('whole_session_driver_observed_wall_s_by_repetition', []) for a in ARMS}
        result['whole_session_basis'] = 'driver-observed session wall including initialization and cleanup'
    else:
        fs = p.get('fixture_summaries', [])
        revisions = fs[0].get('revisions', []) if fs else []
        sequence = fs[0].get('whole_sequence_wall_s_by_arm', {}) if fs else {}
        result['whole_session_basis'] = fs[0].get('whole_sequence_basis') if fs else None
    result['whole_session_times'] = times(sequence)
    result['whole_session_comparisons'] = comparisons(sequence)
    result['whole_session_medians_beat_both_fresh'] = all(
        result['whole_session_times']['candidate_retained']['median_s'] is not None
        and result['whole_session_times'][a]['median_s'] is not None
        and result['whole_session_times']['candidate_retained']['median_s'] < result['whole_session_times'][a]['median_s']
        for a in ('candidate_fresh', 'released_baseline_fresh'))
    for rv in revisions:
        values = rv['wall_s_by_arm']
        c = {'revision': rv['revision'], 'wall': times(values), 'end_to_end_comparisons': comparisons(values)}
        c['acceptance_comparison'] = c['end_to_end_comparisons']['candidate_fresh']
        if path == 'owlapi':
            work = {a: [] for a in ARMS}
            parse = {a: [] for a in ARMS}
            for a in sorted(attempts, key=lambda x: x['repetition']):
                ms = a.get('measurement', {}).get('revisions', [])
                worker = next((r.get('worker', {}) for r in ms if r['revision'] == rv['revision']), {})
                try:
                    work[a['arm']].append((worker['apply_flush_ns'] + worker['taxonomy_publish_and_cleanup_ns']) / 1e9)
                    parse[a['arm']].append(worker['parse_ns'] / 1e9)
                except (KeyError, TypeError):
                    work[a['arm']].append(None)
                    parse[a['arm']].append(None)
            c.update(reasoner_work=times(work), harness_parse=times(parse), reasoner_work_comparisons=comparisons(work))
            c['acceptance_comparison'] = c['reasoner_work_comparisons']['candidate_fresh']
        result['cells'].append(c)
    result['semantics'] = semantic_check(audits)
    complete = (len(result['cells']) == 9 and result['semantics']['four_arm_revisions_checked'] == 45
                and not result['semantics']['differences'] and not binding_errors and result['cleanup_verified']
                and all(c['acceptance_comparison'] is not None for c in result['cells']))
    result['status'] = 'complete' if complete else 'incomplete'
    return result

def main():
    root, plan_file, output = map(Path, sys.argv[1:])
    fixtures = read(plan_file)['fixtures']
    assert len(fixtures) == 80 and sorted(f['index'] for f in fixtures) == list(range(80))
    result = {'schema': 'km-v151-full80-release-summary-v1', 'input_plan_sha256': hashlib.sha256(plan_file.read_bytes()).hexdigest(),
              'candidate_source_commit': '4dd7995b5def62bb8f9140dd2be62b671816f71b',
              'baseline_version': 'v1.5.0', 'baseline_commit': 'd95f0b840a433b5b43c4eff48092e8b600bca8de',
              'candidate_binary_sha256': CANDIDATE, 'baseline_binary_sha256': BASELINE, 'paths': {}}
    for path in ('cli', 'owlapi'):
        cases = [summarize_case(root, path, f) for f in fixtures]
        complete = [c for c in cases if c['status'] == 'complete']
        updates = [dict(ontology=c['ontology'], **r) for c in complete for r in c['cells'] if r['revision'] > 0]
        failures = [dict(ontology=r['ontology'], revision=r['revision'], ratio=r['acceptance_comparison']['median_ratio'])
                    for r in updates if r['acceptance_comparison']['median_ratio'] >= 1]
        result['paths'][path] = dict(cases=cases, scheduled_cases=80, complete_cases=len(complete), scheduled_update_cells=640,
            evaluated_update_cells=len(updates), acceptance_failures=failures,
            missing_or_failed_cases=[c['ontology'] for c in cases if c['status'] != 'complete'],
            whole_sessions_beating_both_fresh=sum(c['whole_session_medians_beat_both_fresh'] for c in complete),
            semantic_differences=sum(len(c.get('semantics', {}).get('differences', [])) for c in cases),
            verified_four_arm_revision_checks=sum(c.get('semantics', {}).get('four_arm_revisions_checked', 0) for c in cases))
        print(path, {k:v for k,v in result['paths'][path].items() if k != 'cases'})
    output.write_text(json.dumps(result, indent=2) + '\n')

if __name__ == '__main__':
    main()
