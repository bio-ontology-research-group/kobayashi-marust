#!/usr/bin/env python3
"""Public OWLAPI four-arm plan/launcher. Full workload execution needs separate authorization."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import sys

_INCREMENTAL_RESULTS = Path(__file__).resolve().parents[2]
_TIMING_RUNNER = _INCREMENTAL_RESULTS / 'timing-runner'
sys.path.insert(0, str(_TIMING_RUNNER))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(_TIMING_RUNNER / 'cleanup-evidence-v3.2-digest'))
from run_panel import ARMS, ORDERS, resolve_inputs, sha256, write_json
from measure_public_owlapi_cleanup_v3 import measure


def cleanup_is_proven_empty(record):
    cleanup = record.get('child_tree_cleanup')
    return (isinstance(cleanup, dict)
            and cleanup.get('status') == 'confirmed_empty_after_cleanup'
            and cleanup.get('remaining_processes') == []
            and cleanup.get('subreaper_restored') is True
            and record.get('remaining_processes') == []
            and record.get('remaining_process_tree_or_group') == []
            and record.get('cleanup_errors') == [])


def preflight(path):
    inventory = json.loads(path.read_text())
    assert inventory['schema'] == 'km-owlapi-four-arm-binding-v1'
    for name, digest in inventory['files'].items():
        assert sha256(name) == digest, 'binding mismatch: ' + name
    variants = inventory['variants']
    assert variants['candidate']['binary'] != variants['released_baseline']['binary']
    assert variants['candidate']['adapter_classes'] != variants['released_baseline']['adapter_classes']
    for name, binding in variants.items():
        assert binding['adapter_classes'] == binding['classpath'].split(':')[0]
        assert 'test-classes' not in binding['classpath']
        assert binding['binary_sha256'] == inventory['files'][binding['binary']]
    return inventory


def canonical(path):
    lines = path.read_text(encoding='utf-8').splitlines()
    assert lines and lines[-1] == 'Z\tcomplete', 'incomplete taxonomy'
    consistent = None
    pairs, unsat, metadata = set(), set(), {}
    for line in lines[:-1]:
        f = line.split('\t')
        if len(f) == 3 and f[0] == 'M':
            assert f[1] not in metadata
            metadata[f[1]] = f[2]
        elif len(f) == 2 and f[0] == 'C':
            assert consistent is None and f[1] in ('true', 'false')
            consistent = f[1] == 'true'
        elif len(f) == 2 and f[0] == 'U':
            assert f[1] and f[1] not in unsat
            unsat.add(f[1])
        elif len(f) == 3 and f[0] == 'S':
            assert f[1] and f[2] and (f[1], f[2]) not in pairs
            pairs.add((f[1], f[2]))
        else:
            raise ValueError('invalid taxonomy record: ' + repr(line))
    assert type(consistent) is bool and metadata['schema'] == '1'
    assert int(metadata['unsatisfiable']) == len(unsat)
    assert int(metadata['subsumptions']) == len(pairs)
    assert int(metadata['classes']) >= len(unsat)
    assert consistent or not (pairs or unsat)
    return {'consistent': consistent, 'unsatisfiable': sorted(unsat),
            'subsumptions': sorted([list(x) for x in pairs])}


def semantic_identity(value):
    """Return compact identity/count fields without materializing serialized JSON."""
    digest = hashlib.sha256()
    encoder = json.JSONEncoder(sort_keys=True, separators=(',', ':'), ensure_ascii=False)
    for chunk in encoder.iterencode(value):
        digest.update(chunk.encode('utf-8'))
    return {'canonical_sha256': digest.hexdigest(), 'consistent': value['consistent'],
            'unsat_count': len(value['unsatisfiable']),
            'subsumption_count': len(value['subsumptions'])}


def audit(attempt, fixture):
    result = []
    last = None
    for index, revision in enumerate(fixture['revisions']):
        row = {'revision': index, 'expected_valid': revision['expected_valid'], 'passed': False}
        try:
            stage = attempt['measurement']['revisions'][index]
            worker = stage['worker']
            if revision['expected_valid']:
                assert worker['status'] == 'executed_unvalidated'
                assert worker['dropped_clauses'] == 0
                path = Path(attempt['output']) / 'session' / f'{index:03}.taxonomy.tsv'
                value = canonical(path)
                if 'expected_consistent' in revision:
                    assert value['consistent'] == revision['expected_consistent']
                for pair in revision.get('entailed', []):
                    assert pair in value['subsumptions'], 'missing independent entailment: ' + repr(pair)
                for pair in revision.get('not_entailed', []):
                    assert pair not in value['subsumptions'], 'unexpected independent entailment: ' + repr(pair)
                if 'expected_unsatisfiable' in revision:
                    assert value['unsatisfiable'] == sorted(revision['expected_unsatisfiable'])
                for sub, sup in revision.get('entailed_if_consistent', []):
                    if value['consistent']:
                        assert sub in value['unsatisfiable'] or [sub, sup] in value['subsumptions'], \
                            'missing asserted added subsumption'
                identity = semantic_identity(value)
                row.update(semantic_identity=identity, taxonomy_sha256=sha256(path))
                last = identity
                del value
            else:
                assert worker['status'] == 'operation_error'
                assert revision['expected_error_substring'] in worker['exception_message']
                if attempt['arm'].endswith('_retained'):
                    assert worker['rollback_snapshot_available'] is True and last is not None
                    path = Path(attempt['output']) / 'session' / f'{index:03}.rollback.taxonomy.tsv'
                    rollback_identity = semantic_identity(canonical(path))
                    assert rollback_identity == last, 'rejected update changed the committed hierarchy'
                    row['rollback_sha256'] = sha256(path)
                    row['rollback_semantic_identity'] = rollback_identity
            row['passed'] = True
        except Exception as error:
            row['error'] = repr(error)
        result.append(row)
    return result


def summarize(fixture, attempts, repetitions):
    rows = []
    for index, revision in enumerate(fixture['revisions']):
        times = {arm: [] for arm in ARMS}
        for attempt in attempts:
            values = attempt.get('measurement', {}).get('revisions', [])
            times[attempt['arm']].append(values[index].get('wall_s') if index < len(values) else None)
        ratios = [a / b for a, b in zip(times['candidate_retained'], times['candidate_fresh'])
                  if isinstance(a, (int, float)) and isinstance(b, (int, float)) and b > 0]
        before = [a / b for a, b in zip(times['candidate_retained'], times['released_baseline_retained'])
                  if isinstance(a, (int, float)) and isinstance(b, (int, float)) and b > 0]
        rows.append({'revision': index, 'operation': revision['operation'], 'label': revision['label'],
                     'expected_valid': revision['expected_valid'], 'wall_s_by_arm': times,
                     'candidate_retained_over_candidate_fresh_per_pair': ratios,
                     'candidate_retained_over_released_retained_per_pair': before,
                     'median_candidate_retained_over_candidate_fresh': statistics.median(ratios) if len(ratios) == repetitions else None,
                     'update_case': revision['operation'] == 'replace' and revision['expected_valid']})
    sequences = {arm: [a['measurement'].get('comparable_whole_sequence_wall_s') for a in attempts if a['arm'] == arm] for arm in ARMS}
    return {'revisions': rows, 'whole_sequence_wall_s_by_arm': sequences,
            'initialization': 'revision0 is reported separately; launch-to-READY is additionally reported per attempt',
            'whole_sequence_basis': 'launch-to-READY + sum complete DONE event calls + observed process shutdown; harness gaps excluded',
            'performance_acceptance': 'not inferred by this preparation/smoke runner; all cases, statuses and ratios preserved'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bindings', type=Path, required=True)
    parser.add_argument('--protocol', type=Path, required=True)
    parser.add_argument('--fixtures', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--cpu', type=int, default=None)
    parser.add_argument('--preflight-only', action='store_true')
    parser.add_argument('--smoke', action='store_true', help='one repetition, at most two tiny fixtures; no timing claim')
    args = parser.parse_args()
    inventory = preflight(args.bindings)
    from run_panel import validate_protocol
    validate_protocol(json.loads(args.protocol.read_text()))
    fixtures = resolve_inputs(json.loads(args.fixtures.read_text()), args.fixtures)
    if args.preflight_only:
        print(json.dumps({'status': 'preflight_passed_not_run', 'fixtures': len(fixtures)}))
        return
    if not args.output:
        parser.error('--output required for execution')
    cpu = args.cpu if args.cpu is not None else min(os.sched_getaffinity(0))
    assert cpu in os.sched_getaffinity(0)
    os.sched_setaffinity(0, {cpu})
    repetitions = 1 if args.smoke else 5
    if args.smoke:
        assert len(fixtures) <= 2 and all(len(f['revisions']) <= 5 for f in fixtures)
        assert all(Path(r['path']).stat().st_size <= 16384 for f in fixtures for r in f['revisions'])
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    top = {'schema': 'km-owlapi-panel-digest-v1', 'semantic_identity_schema': 'canonical-sha256-counts-v1', 'status': 'running', 'binding_sha256': sha256(args.bindings), 'protocol_sha256': sha256(args.protocol),
           'fixtures_sha256': sha256(args.fixtures), 'driver_sha256': sha256(__file__),
           'balanced_arm_orders': [list(order) for order in ORDERS[:repetitions]],
           'repetitions': repetitions, 'smoke_only': args.smoke, 'performance_claim': False,
           'attempts': [], 'fixture_summaries': []}
    write_json(output / 'panel.json', top)
    complete = True
    cleanup_failed = False
    for fixture_index, fixture in enumerate(fixtures):
        attempts = []
        for repetition in range(repetitions):
            for arm_index, arm in enumerate(ORDERS[repetition]):
                name = 'candidate' if arm.startswith('candidate_') else 'released_baseline'
                mode = 'retained' if arm.endswith('_retained') else 'fresh'
                arm_out = output / fixture['id'] / f'repetition-{repetition:02}' / arm
                arm_out.parent.mkdir(parents=True, exist_ok=True)
                attempt = {'arm': arm, 'fixture_id': fixture['id'], 'repetition': repetition, 'output': str(arm_out),
                           'semantic_identity_schema': 'canonical-sha256-counts-v1'}
                top['attempts'].append(attempt)
                write_json(output / 'panel.json', top)
                measured = measure(inventory['variants'][name], fixture['revisions'], mode, arm_out,
                                   cpu, timeout=60 if args.smoke else 240, heap='1g' if args.smoke else '16g')
                attempt['measurement'] = measured
                attempt['semantic_audit'] = audit(attempt, fixture)
                attempt['record_sha256'] = sha256(arm_out / 'record.json')
                attempts.append(attempt)
                cleanup_ok = cleanup_is_proven_empty(measured)
                attempt['cleanup_proven_empty'] = cleanup_ok
                complete &= (measured['status'] == 'executed_unvalidated'
                             and cleanup_ok
                             and all(x['passed'] for x in attempt['semantic_audit']))
                write_json(output / 'panel.json', top)
                if not cleanup_ok:
                    cleanup_failed = True
                    top['status'] = 'stopped_cleanup_unproven'
                    top['stop_reason'] = 'OWLAPI child-tree cleanup proof missing, live, or unconfirmed'
                    skipped = []
                    for later_rep in range(repetition, repetitions):
                        start_at = arm_index + 1 if later_rep == repetition else 0
                        for later_arm in ORDERS[later_rep][start_at:]:
                            skipped.append({'fixture_id': fixture['id'], 'repetition': later_rep,
                                            'arm': later_arm, 'reason': 'cleanup_unproven'})
                    for later_fixture in fixtures[fixture_index + 1:]:
                        for later_rep, order in enumerate(ORDERS[:repetitions]):
                            for later_arm in order:
                                skipped.append({'fixture_id': later_fixture['id'],
                                                'repetition': later_rep, 'arm': later_arm,
                                                'reason': 'cleanup_unproven'})
                    top['skipped_after_cleanup_failure'] = skipped
                    write_json(output / 'panel.json', top)
                    break
            if cleanup_failed:
                break
        if cleanup_failed:
            top['fixture_summaries'].append({'fixture_id': fixture['id'], **summarize(fixture, attempts, repetitions)})
            break
        current = attempts[-4:]
        for index, revision in enumerate(fixture['revisions']):
            if revision['expected_valid']:
                values = [a['semantic_audit'][index].get('semantic_identity') for a in current]
                complete &= values[0] is not None and all(v == values[0] for v in values)
        top['fixture_summaries'].append({'fixture_id': fixture['id'], **summarize(fixture, attempts, repetitions)})
    preflight(args.bindings)
    assert sha256(args.fixtures) == top['fixtures_sha256']
    assert all(sha256(r['path']) == r['sha256'] for f in fixtures for r in f['revisions'])
    if not cleanup_failed:
        top.update(status='complete_semantic_smoke' if complete and args.smoke else 'complete_execution_and_parity' if complete else 'completed_with_failures',
               postflight_pins_identical=True)
    from evaluate_public_owlapi_digest import evaluate
    top['performance_acceptance'] = evaluate(top, fixtures, inventory)
    write_json(output / 'panel.json', top)
    print(json.dumps({'status': top['status'], 'attempts': len(top['attempts']), 'panel_sha256': sha256(output / 'panel.json')}))
    if not complete:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
