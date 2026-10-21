#!/usr/bin/env python3
"""Run the fixed four-arm KM incremental panel from explicit pinned manifests.

This is an execution harness only. It records every attempt and raw response;
the separate semantic audit never substitutes for a missing execution result.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import statistics
import time

import measure_classification_cleanup_v3 as measure_classification
import measure_retained_km_cleanup_v3 as measure_retained_km


ARMS = ('candidate_retained', 'candidate_fresh',
        'released_baseline_retained', 'released_baseline_fresh')
ORDERS = (
    ARMS,
    (ARMS[1], ARMS[2], ARMS[3], ARMS[0]),
    (ARMS[2], ARMS[3], ARMS[0], ARMS[1]),
    (ARMS[3], ARMS[0], ARMS[1], ARMS[2]),
    (ARMS[0], ARMS[3], ARMS[1], ARMS[2]),
)


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def write_json(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.part')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    temporary.replace(path)


def load_json(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def resolve_manifest_path(value, manifest_path):
    path = Path(value)
    return (path if path.is_absolute() else Path(manifest_path).resolve().parent / path).resolve()


def resolve_inputs(manifest, manifest_path):
    if manifest.get('schema') != 1 or not isinstance(manifest.get('fixtures'), list) or not manifest['fixtures']:
        raise ValueError('input manifest must have schema=1 and a nonempty fixtures array')
    seen_ids = set()
    resolved = []
    for fixture in manifest['fixtures']:
        fixture_id = fixture.get('id')
        revisions = fixture.get('revisions')
        if not isinstance(fixture_id, str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,95}', fixture_id) or fixture_id in seen_ids:
            raise ValueError(f'invalid or duplicate fixture id: {fixture_id!r}')
        seen_ids.add(fixture_id)
        if not isinstance(revisions, list) or not revisions:
            raise ValueError(f'{fixture_id}: revisions must be nonempty')
        cooked = []
        for index, revision in enumerate(revisions):
            item = dict(revision)
            if index == 0 and item.get('operation') != 'init':
                raise ValueError(f'{fixture_id}: first revision operation must be init')
            if item.get('operation') not in ('init', 'replace', 'classify'):
                raise ValueError(f'{fixture_id}: unsupported operation {item.get("operation")!r}')
            item['path'] = str(resolve_manifest_path(item.get('path', ''), manifest_path))
            if not Path(item['path']).is_file():
                raise ValueError(f'{fixture_id}: missing revision input {item["path"]}')
            actual = sha256(item['path'])
            if actual != item.get('sha256'):
                raise ValueError(f'{fixture_id}: input hash mismatch for {item["path"]}')
            if type(item.get('expected_valid')) is not bool:
                raise ValueError(f'{fixture_id}: every revision needs boolean expected_valid')
            expected_response = item.get('expected_response_status', 'ok')
            if expected_response not in ('ok', 'error'):
                raise ValueError(f'{fixture_id}: expected_response_status must be ok or error')
            if item['expected_valid'] != (expected_response == 'ok'):
                raise ValueError(f'{fixture_id}: expected_valid and response status conflict')
            if not item['expected_valid'] and (not isinstance(item.get('expected_error_substring'), str)
                                               or not item['expected_error_substring']):
                raise ValueError(f'{fixture_id}: invalid revision must pin expected_error_substring')
            if item['operation'] == 'classify' and not item['expected_valid']:
                raise ValueError(f'{fixture_id}: classify row must identify a valid resulting snapshot')
            item['revision'] = index
            item['label'] = item.get('label', f'revision-{index}')
            if not isinstance(item['label'], str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,95}', item['label']):
                raise ValueError(f'{fixture_id}: unsafe revision label {item["label"]!r}')
            item['expected_response_status'] = expected_response
            cooked.append(item)
        resolved.append({'id': fixture_id, 'revisions': cooked})
    return resolved


def validate_protocol(protocol):
    if protocol.get('measurement_protocol', {}).get('repetitions') != 5:
        raise ValueError('this driver is fixed to the reviewed five-repetition protocol')
    resources = protocol.get('measurement_protocol', {}).get('resources', {})
    if resources.get('cpu_threads') != 1 or resources.get('memory_mib') != 20480 or resources.get('per_classification_or_update_timeout_s') != 240:
        raise ValueError('protocol resource caps differ from reviewed 1 CPU, 20480 MiB, 240 seconds')
    if protocol.get('performance_acceptance', {}).get('provisional_per_case_rule', {}).get('required_ratio_max') != 0.8:
        raise ValueError('protocol per-case acceptance threshold changed; review driver before use')
    return protocol['measurement_protocol'].get('km_environment', {'KM_ROUTE': 'auto', 'KM_THREADS': '1'})


def validate_binaries(inventory, inventory_path):
    arms = inventory.get('arms')
    if inventory.get('schema') != 1 or not isinstance(arms, dict):
        raise ValueError('binary inventory must have schema=1 and arms object')
    resolved = {}
    for name in ('candidate', 'released_baseline'):
        row = arms.get(name)
        if not isinstance(row, dict) or not row.get('path') or not row.get('sha256'):
            raise ValueError(f'binary inventory missing pinned {name}')
        path = resolve_manifest_path(row['path'], inventory_path)
        if not path.is_file() or not os.access(path, os.X_OK) or sha256(path) != row['sha256']:
            raise ValueError(f'{name} binary absent or hash mismatch: {path}')
        if not isinstance(row.get('source_manifest_sha256'), str) or not row['source_manifest_sha256']:
            raise ValueError(f'{name} binary inventory must bind source_manifest_sha256')
        if not isinstance(row.get('build_receipt_sha256'), str) or not row['build_receipt_sha256']:
            raise ValueError(f'{name} binary inventory must bind build_receipt_sha256')
        for path_key, hash_key in (('source_manifest_path', 'source_manifest_sha256'),
                                   ('build_receipt_path', 'build_receipt_sha256')):
            if not row.get(path_key):
                raise ValueError(f'{name} binary inventory must bind {path_key}')
            receipt_path = resolve_manifest_path(row[path_key], inventory_path)
            if not receipt_path.is_file() or sha256(receipt_path) != row[hash_key]:
                raise ValueError(f'{name} {path_key} missing or hash mismatch: {receipt_path}')
            row[f'resolved_{path_key}'] = str(receipt_path)
        build = load_json(row['resolved_build_receipt_path'])
        bound_binary = build.get('binary_sha256', build.get('artifact_sha256'))
        if bound_binary != row['sha256']:
            raise ValueError(f'{name} build receipt does not bind its binary hash')
        if build.get('source_manifest_sha256') not in (None, row['source_manifest_sha256']):
            raise ValueError(f'{name} build receipt source manifest hash mismatch')
        resolved[name] = {**row, 'path': str(path)}
    if resolved['candidate']['sha256'] == resolved['released_baseline']['sha256']:
        raise ValueError('candidate and released baseline binary hashes are identical')
    return resolved


def semantic_digest(view):
    """Hash the canonical JSON stream without building another JSON byte string."""
    digest = hashlib.sha256()
    encoder = json.JSONEncoder(sort_keys=True, separators=(',', ':'), ensure_ascii=False)
    for chunk in encoder.iterencode(view):
        digest.update(chunk.encode('utf-8'))
    return {'canonical_sha256': digest.hexdigest(), 'consistent': view['consistent'],
            'unsat_count': len(view['unsatisfiable']),
            'subsumption_count': len(view['nonreflexive_nonunsat_subsumptions']),
            'dropped': view['dropped']}


def canonical_result(value):
    """Validate result shape and produce a deterministic, filtered answer view."""
    result = value.get('result', value) if isinstance(value, dict) else None
    if not isinstance(result, dict):
        raise ValueError('classification result is not an object')
    consistent = result.get('consistent')
    dropped = result.get('dropped')
    unsat = result.get('unsatisfiable')
    pairs = result.get('subsumptions')
    if type(consistent) is not bool:
        raise ValueError('consistent must be boolean')
    if type(dropped) is not int or dropped != 0:
        raise ValueError(f'dropped must be integer zero, got {dropped!r}')
    if not isinstance(unsat, list) or any(not isinstance(c, str) for c in unsat):
        raise ValueError('unsatisfiable must be an array of strings')
    if not isinstance(pairs, list):
        raise ValueError('subsumptions must be an array')
    for pair in pairs:
        if not isinstance(pair, list) or len(pair) != 2 or any(not isinstance(c, str) for c in pair):
            raise ValueError(f'invalid subsumption pair {pair!r}')
    unsat_set = set(unsat)
    normalized = sorted({(sub, sup) for sub, sup in pairs
                         if sub != sup and sub not in unsat_set and sup not in unsat_set})
    return {'consistent': consistent, 'unsatisfiable': sorted(unsat_set),
            'nonreflexive_nonunsat_subsumptions': [list(pair) for pair in normalized], 'dropped': 0}


def retained_rows(record, revisions):
    by_index = {r.get('revision'): r for r in record.get('revisions', [])}
    failure = next((r for r in record.get('revisions', [])
                    if r.get('status') not in ('executed_unvalidated', 'expected_refusal_unvalidated')), None)
    for revision in revisions:
        row = by_index.get(revision['revision'])
        if row is None:
            continue
        if row.get('status') == 'not_run_after_session_failure':
            row['status'] = 'skipped_after_session_failure'
            row['skip_cause'] = ({'revision': failure.get('revision'), 'status': failure.get('status')}
                                 if failure else {'status': record.get('status')})
    return record


def run_retained(binary, revisions, output, timeout, memory_mib, km_overrides):
    row = {'path': binary['path'], 'sha256': binary['sha256']}
    return measure_retained_km.measure(row, revisions, output, timeout=timeout,
                                       memory_mib=memory_mib, km_overrides=km_overrides)


def cleanup_is_proven_empty(record):
    cleanup = record.get('child_tree_cleanup')
    return (isinstance(cleanup, dict)
            and cleanup.get('status') == 'confirmed_empty_after_cleanup'
            and cleanup.get('remaining_processes') == []
            and cleanup.get('subreaper_restored') is True
            and record.get('remaining_processes') == [])


def run_fresh(binary, revisions, output, timeout, memory_mib, km_overrides, time_binary):
    artifacts = [{'id': 'km', 'path': binary['path'], 'sha256': binary['sha256']}]
    inventory = {'artifacts': artifacts}
    records = []
    for revision in revisions:
        destination = Path(output) / f"revision-{revision['revision']:03d}-{revision['label']}"
        try:
            row = measure_classification.measure(
                inventory, 'km', revision['path'], revision['sha256'], destination,
                timeout=timeout, memory_mib=memory_mib, time_binary=time_binary,
                km_overrides=km_overrides)
        except Exception as error:  # preserve step-level adapter failures and continue
            row = {'status': 'adapter_error', 'error': str(error), 'revision': revision['revision'],
                   'source_path': revision['path'], 'source_sha256': revision['sha256']}
        row['revision'] = revision['revision']
        row['expected_valid'] = revision['expected_valid']
        records.append(row)
        if not cleanup_is_proven_empty(row):
            for skipped in revisions[revision['revision'] + 1:]:
                records.append({'revision': skipped['revision'], 'expected_valid': skipped['expected_valid'],
                                'status': 'not_run_after_cleanup_unproven',
                                'skip_cause_revision': revision['revision']})
            break
    return records


def load_measurement(attempt):
    if isinstance(attempt.get('measurement'), dict):
        return attempt['measurement']
    path = attempt.get('measurement_path')
    if path and Path(path).is_file():
        return load_json(path)
    return {}


def load_arm_result(output, arm_record, revision):
    index = revision['revision']
    if arm_record['arm'].endswith('_retained'):
        record = load_measurement(arm_record)
        stage = next((r for r in record.get('revisions', []) if r.get('revision') == index), None)
        if stage is None or stage.get('status') != 'executed_unvalidated':
            return {'status': stage.get('status') if stage else 'missing_step', 'source': stage}
        path = Path(arm_record['output']) / f'{index:03}.response.json'
        if not path.is_file():
            return {'status': 'missing_raw_response', 'path': str(path)}
        response = load_json(path)
        return {'status': response.get('status'), 'response': response, 'raw_path': str(path), 'raw_sha256': sha256(path)}
    fresh_row = next((r for r in arm_record.get('measurements', []) if r.get('revision') == index), None)
    if fresh_row is None or fresh_row.get('status') != 'executed_unvalidated':
        return {'status': fresh_row.get('status') if fresh_row else 'missing_step', 'source': fresh_row,
                'measurement': fresh_row}
    path = Path(arm_record['output']) / f"revision-{index:03d}-{revision['label']}" / 'taxonomy.raw'
    if not path.is_file():
        return {'status': 'missing_raw_taxonomy', 'path': str(path)}
    return {'status': 'ok', 'result': load_json(path), 'raw_path': str(path), 'raw_sha256': sha256(path)}


def audit_fixture(fixture, attempts, output):
    audits = []
    for revision in fixture['revisions']:
        row = {'revision': revision['revision'], 'label': revision['label'],
               'expected_valid': revision['expected_valid'], 'arms': {}}
        valid_views = {}
        for arm in ARMS:
            attempt = next((a for a in attempts if a['arm'] == arm), None)
            # Each repetition is audited independently below; this per-fixture
            # routine is called once per repetition and receives that subset.
            if attempt is None:
                row['arms'][arm] = {'status': 'missing_attempt'}
                continue
            loaded = load_arm_result(output, attempt, revision)
            entry = {'status': loaded['status'], 'raw_path': loaded.get('raw_path'), 'raw_sha256': loaded.get('raw_sha256')}
            if revision['expected_valid'] and loaded['status'] == 'ok':
                try:
                    result = loaded.get('response', loaded.get('result'))
                    view = canonical_result(result)
                    identity = semantic_digest(view)
                    entry.update(semantic_status='valid', semantic_identity=identity)
                    valid_views[arm] = identity
                    del view
                    del result
                except Exception as error:
                    entry.update(semantic_status='invalid_output', semantic_error=str(error))
            elif not revision['expected_valid']:
                expected = revision['expected_response_status']
                entry['semantic_status'] = 'refusal_or_invalid_input_not_compared'
                if arm.endswith('_retained'):
                    measurement = load_measurement(attempt)
                    stage = next((s for s in measurement.get('revisions', []) if s.get('revision') == revision['revision']), {})
                    expected_text = revision['expected_error_substring']
                    entry['retained_error_excerpt'] = stage.get('response_error')
                    entry['expected_retained_response_observed'] = (
                        stage.get('status') == 'expected_refusal_unvalidated'
                        and stage.get('actual_response_status') == expected
                        and expected_text in (stage.get('response_error') or ''))
                else:
                    measurement = loaded.get('measurement') or {}
                    entry['fresh_terminal_status'] = measurement.get('status')
                    entry['fresh_exit_code'] = measurement.get('exit_code')
                    entry['fresh_stderr'] = measurement.get('files', {}).get('stderr')
                    stderr_path = (Path(attempt['output']) / f"revision-{revision['revision']:03d}-{revision['label']}" / 'stderr')
                    excerpt = stderr_path.read_bytes()[:8192].decode('utf-8', 'replace') if stderr_path.is_file() else ''
                    entry['fresh_stderr_excerpt'] = excerpt
                    entry['expected_fresh_refusal_observed'] = (
                        measurement.get('status') == 'process_error'
                        and isinstance(measurement.get('exit_code'), int)
                        and measurement['exit_code'] != 0
                        and revision['expected_error_substring'] in excerpt)
            row['arms'][arm] = entry
            if loaded is not None:
                del loaded
        if revision['expected_valid']:
            row['retained_equals_fresh'] = {
                'candidate': valid_views.get('candidate_retained') == valid_views.get('candidate_fresh')
                             if 'candidate_retained' in valid_views and 'candidate_fresh' in valid_views else None,
                'released_baseline': valid_views.get('released_baseline_retained') == valid_views.get('released_baseline_fresh')
                                     if 'released_baseline_retained' in valid_views and 'released_baseline_fresh' in valid_views else None,
            }
            row['candidate_fresh_equals_released_fresh'] = (
                valid_views['candidate_fresh'] == valid_views['released_baseline_fresh']
                if 'candidate_fresh' in valid_views and 'released_baseline_fresh' in valid_views else None)
        audits.append(row)
    return audits


def median_or_none(values):
    return statistics.median(values) if values and all(isinstance(v, (int, float)) for v in values) else None


def summarize_fixture(fixture, attempts):
    by_arm_rep = {(a['arm'], a['repetition']): a for a in attempts}
    cases = []
    for revision in fixture['revisions']:
        if not revision['expected_valid']:
            continue
        walls = {arm: [] for arm in ARMS}
        for rep in range(5):
            for arm in ARMS:
                attempt = by_arm_rep.get((arm, rep), {})
                if arm.endswith('_retained'):
                    measurement = load_measurement(attempt)
                    stage = next((s for s in measurement.get('revisions', []) if s.get('revision') == revision['revision']), {})
                    wall = stage.get('wall_s') if stage.get('status') == 'executed_unvalidated' else None
                else:
                    measurement = next((m for m in attempt.get('measurements', []) if m.get('revision') == revision['revision']), {})
                    wall = measurement.get('wall_s') if measurement.get('status') == 'executed_unvalidated' else None
                walls[arm].append(wall)
        paired = [a / b for a, b in zip(walls['candidate_retained'], walls['candidate_fresh'])
                  if isinstance(a, (int, float)) and isinstance(b, (int, float)) and b > 0]
        before_after = [a / b for a, b in zip(walls['candidate_retained'], walls['released_baseline_retained'])
                        if isinstance(a, (int, float)) and isinstance(b, (int, float)) and b > 0]
        ratio = median_or_none(paired)
        cases.append({'revision': revision['revision'], 'label': revision['label'],
                      'operation': revision['operation'],
                      'update_threshold_applies': revision['operation'] == 'replace',
                      'attempted_pairs': {key: sum(v is not None for v in value) for key, value in walls.items()},
                      'wall_s_by_arm': walls, 'candidate_retained_over_candidate_fresh_ratio_per_pair': paired,
                      'median_candidate_retained_over_candidate_fresh_ratio': ratio,
                      'provisional_ratio_threshold_pass': (len(paired) == 5 and ratio <= 0.8
                                                           if revision['operation'] == 'replace' else None),
                      'candidate_retained_over_released_retained_ratio_per_pair': before_after,
                      'median_candidate_retained_over_released_retained_ratio': median_or_none(before_after)})
    session = {}
    for arm in ARMS:
        driver_totals, comparable_totals = [], []
        for rep in range(5):
            attempt = by_arm_rep.get((arm, rep), {})
            driver_totals.append(attempt.get('adapter_wall_s'))
            if arm.endswith('_retained'):
                measurement = load_measurement(attempt)
                steps = measurement.get('revisions', [])
                all_recorded = (len(steps) == len(fixture['revisions']) and all(
                    s.get('status') == ('executed_unvalidated' if rev['expected_valid'] else 'expected_refusal_unvalidated')
                    and isinstance(s.get('wall_s'), (int, float))
                    for s, rev in zip(steps, fixture['revisions'])))
                comparable = measurement.get('comparable_whole_session_wall_s') if all_recorded else None
            else:
                rows = attempt.get('measurements', [])
                times = [r.get('wall_s') for r in rows]
                accounted = (len(rows) == len(fixture['revisions']) and all(
                    (r.get('status') == 'executed_unvalidated' if rev['expected_valid'] else r.get('status') == 'process_error')
                    and isinstance(r.get('wall_s'), (int, float))
                    for r, rev in zip(rows, fixture['revisions'])))
                comparable = sum(times) if accounted else None
            comparable_totals.append(comparable)
        session[arm] = {
            'whole_session_driver_observed_wall_s_by_repetition': driver_totals,
            'median_whole_session_driver_observed_wall_s': median_or_none(driver_totals),
            'comparable_engine_and_api_work_wall_s_by_repetition': comparable_totals,
            'median_comparable_engine_and_api_work_wall_s': median_or_none(comparable_totals),
        }
    candidate = session['candidate_retained']['median_whole_session_driver_observed_wall_s']
    for name in ('candidate_fresh', 'released_baseline_fresh'):
        fresh = session[name]['median_whole_session_driver_observed_wall_s']
        session[f'candidate_retained_below_{name}'] = candidate < fresh if candidate is not None and fresh is not None else None
        comparable_fresh = session[name]['median_comparable_engine_and_api_work_wall_s']
        comparable_candidate = session['candidate_retained']['median_comparable_engine_and_api_work_wall_s']
        session[f'candidate_retained_comparable_work_below_{name}'] = (
            comparable_candidate < comparable_fresh
            if comparable_candidate is not None and comparable_fresh is not None else None)
    return {'fixture_id': fixture['id'], 'per_valid_revision': cases, 'whole_session': session}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--protocol', type=Path, required=True)
    parser.add_argument('--binary-inventory', type=Path, required=True)
    parser.add_argument('--fixture-manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--time-binary', default=None,
                        help='optional /usr/bin/time path; default null relies on tree RSS watchdog')
    args = parser.parse_args()
    protocol = load_json(args.protocol)
    km_overrides = validate_protocol(protocol)
    binaries = validate_binaries(load_json(args.binary_inventory), args.binary_inventory)
    fixtures = resolve_inputs(load_json(args.fixture_manifest), args.fixture_manifest)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    top = {'schema': 1, 'semantic_identity_schema': 'canonical-sha256-counts-v1', 'status': 'running', 'protocol_path': str(args.protocol.resolve()),
           'protocol_sha256': sha256(args.protocol), 'binary_inventory_path': str(args.binary_inventory.resolve()),
           'binary_inventory_sha256': sha256(args.binary_inventory),
           'fixture_manifest_path': str(args.fixture_manifest.resolve()),
           'fixture_manifest_sha256': sha256(args.fixture_manifest), 'km_overrides': km_overrides,
           'time_binary': args.time_binary,
           'timeout_s': 240, 'memory_mib': 20480, 'cpu_threads': 1, 'repetitions': 5,
           'balanced_arm_orders': [list(x) for x in ORDERS], 'expected_attempt_count': 20 * len(fixtures),
           'fixtures': [], 'attempts': []}
    write_json(output / 'panel.json', top)
    all_complete = True
    for fixture in fixtures:
        fixture_out = output / fixture['id']
        fixture_out.mkdir()
        fixture_attempts = []
        for repetition in range(5):
            for arm in ORDERS[repetition]:
                binary_name = 'candidate' if arm.startswith('candidate_') else 'released_baseline'
                binary = binaries[binary_name]
                arm_out = fixture_out / f'repetition-{repetition:02d}' / arm
                arm_out.parent.mkdir(parents=True, exist_ok=True)
                started = time.monotonic()
                attempt = {'fixture_id': fixture['id'], 'repetition': repetition, 'arm': arm,
                           'binary_path': binary['path'], 'binary_sha256': binary['sha256'],
                           'binary_inventory_binding': binary,
                           'order_position': list(ORDERS[repetition]).index(arm),
                           'output': str(arm_out), 'status': 'running'}
                fixture_attempts.append(attempt)
                top['attempts'].append(attempt)
                write_json(output / 'panel.json', top)
                record = {}
                try:
                    if arm.endswith('_retained'):
                        record = run_retained(binary, fixture['revisions'], arm_out, 240, 20480, km_overrides)
                        record = retained_rows(record, fixture['revisions'])
                        write_json(arm_out / 'record.json', record)
                        attempt['measurement_path'] = str((arm_out / 'record.json').resolve())
                        attempt['measurement_sha256'] = sha256(arm_out / 'record.json')
                        attempt['status'] = record.get('status', 'unknown')
                    else:
                        attempt['measurements'] = run_fresh(binary, fixture['revisions'], arm_out, 240, 20480,
                                                            km_overrides, args.time_binary)
                        expected_terminal = all(
                            (m.get('status') == 'executed_unvalidated' if rev['expected_valid']
                             else m.get('status') == 'process_error')
                            for m, rev in zip(attempt['measurements'], fixture['revisions']))
                        attempt['status'] = 'terminal_steps_recorded' if expected_terminal else 'partial_or_failed'
                except Exception as error:
                    attempt.update(status='adapter_error', error=str(error))
                    all_complete = False
                attempt['adapter_wall_s'] = time.monotonic() - started
                if arm.endswith('_retained'):
                    cleanup_ok = cleanup_is_proven_empty(record)
                else:
                    cleanup_ok = bool(attempt.get('measurements')) and all(
                        cleanup_is_proven_empty(m) for m in attempt['measurements']
                        if m.get('status') != 'not_run_after_cleanup_unproven')
                    cleanup_ok = cleanup_ok and all(
                        m.get('status') != 'not_run_after_cleanup_unproven'
                        for m in attempt.get('measurements', []))
                attempt['cleanup_proven_empty'] = cleanup_ok
                write_json(output / 'panel.json', top)
                if not cleanup_ok:
                    attempt['status'] = 'cleanup_unproven'
                    top['status'] = 'stopped_cleanup_unproven'
                    top['stop_reason'] = {'fixture_id': fixture['id'], 'repetition': repetition,
                                          'arm': arm, 'attempt_index': len(top['attempts']) - 1}
                    write_json(output / 'panel.json', top)
                    print(json.dumps({'status': top['status'], 'attempt_count': len(top['attempts']),
                                      'expected_attempt_count': top['expected_attempt_count'],
                                      'stop_reason': top['stop_reason']}))
                    return
        for repetition in range(5):
            subset = [a for a in fixture_attempts if a['repetition'] == repetition]
            audits = audit_fixture(fixture, subset, output)
            for audit in audits:
                audit['repetition'] = repetition
            write_json(fixture_out / f'semantic-audit-repetition-{repetition:02d}.json',
                       {'fixture_id': fixture['id'], 'repetition': repetition, 'revisions': audits})
            for audit in audits:
                if audit.get('retained_equals_fresh'):
                    if audit['retained_equals_fresh'].get('candidate') is not True or audit['retained_equals_fresh'].get('released_baseline') is not True:
                        all_complete = False
                    if audit.get('candidate_fresh_equals_released_fresh') is not True:
                        all_complete = False
                elif audit['expected_valid'] is False:
                    for arm in ('candidate_retained', 'released_baseline_retained'):
                        if audit['arms'][arm].get('expected_retained_response_observed') is not True:
                            all_complete = False
                    for arm in ('candidate_fresh', 'released_baseline_fresh'):
                        if audit['arms'][arm].get('expected_fresh_refusal_observed') is not True:
                            all_complete = False
        if any(a['status'] not in ('executed_unvalidated', 'terminal_steps_recorded') for a in fixture_attempts):
            all_complete = False
        write_json(fixture_out / 'timing-summary.json', summarize_fixture(fixture, fixture_attempts))
        top['fixtures'].append({'id': fixture['id'], 'attempt_count': len(fixture_attempts),
                                'semantic_audit_files': [f'semantic-audit-repetition-{i:02d}.json' for i in range(5)],
                                'semantic_identity_schema': 'canonical-sha256-counts-v1'})
        write_json(output / 'panel.json', top)
    top['status'] = 'complete_execution_and_semantic_audit' if all_complete else 'completed_with_failures_or_semantic_mismatches'
    top['owlapi_status'] = 'not_run_by_this_cli_panel_driver'
    summaries = [load_json(output / fixture['id'] / 'timing-summary.json') for fixture in fixtures]
    case_rows = [case for summary in summaries for case in summary['per_valid_revision']
                 if case['update_threshold_applies']]
    case_rule = (all(case['provisional_ratio_threshold_pass'] for case in case_rows)
                 if case_rows and all(case['provisional_ratio_threshold_pass'] is not None for case in case_rows)
                 else None)
    session_rules = [summary['whole_session'].get('candidate_retained_comparable_work_below_candidate_fresh') is True
                     and summary['whole_session'].get('candidate_retained_comparable_work_below_released_baseline_fresh') is True
                     for summary in summaries]
    top['performance_acceptance'] = {
        'status': ('pass_provisional_rules' if all_complete and case_rule is True and all(session_rules)
                   else 'fail_or_incomplete' if case_rows else 'not_evaluable'),
        'provisional_candidate_retained_over_candidate_fresh_ratio_rule_all_valid_steps_pass': case_rule,
        'whole_session_candidate_retained_below_both_fresh_sequences_all_fixtures': all(session_rules) if summaries else None,
        'valid_update_case_count': len(case_rows),
        'threshold_ratio_max': 0.8,
        'initialization_and_classify_queries_reported_separately_from_updates': True,
        'whole_session_basis': 'spawn + all timed API calls including initialization + shutdown; evidence-file writes excluded',
        'candidate_retained_vs_released_retained_ratios_reported_per_case': True,
        'no_population_averaging_substituted_for_per_case_rule': True,
    }
    write_json(output / 'panel.json', top)
    print(json.dumps({'status': top['status'], 'fixture_count': len(fixtures),
                      'attempt_count': len(top['attempts']), 'owlapi_status': top['owlapi_status']}))


if __name__ == '__main__':
    main()
