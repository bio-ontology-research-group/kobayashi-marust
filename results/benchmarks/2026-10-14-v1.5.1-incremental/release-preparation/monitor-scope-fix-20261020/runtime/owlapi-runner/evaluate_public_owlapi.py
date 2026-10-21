"""Fail-closed per-case evaluator. Reopens raw artifacts; cached pass flags are ignored."""
import argparse
import json
import math
from pathlib import Path
import statistics


ARMS = ('candidate_retained', 'candidate_fresh', 'released_baseline_retained', 'released_baseline_fresh')


def number(value):
    return type(value) in (float, int) and math.isfinite(value) and value > 0


def evaluate(panel, fixtures, bindings=None):
    # Lazy import avoids a cycle when the launcher invokes this after writing
    # all terminal measurements. canonical/audit parse actual TSV output.
    from run_four_arm import audit, sha256
    problems, checked, summaries = [], {}, []
    expected = {(f['id'], rep, arm) for f in fixtures for rep in range(5) for arm in ARMS}
    actual = [(a.get('fixture_id'), a.get('repetition'), a.get('arm')) for a in panel.get('attempts', [])]
    if len(actual) != len(set(actual)) or set(actual) != expected or panel.get('repetitions') != 5:
        problems.append('expected exactly five distinct paired repetitions of all four arms for every fixture')
    by_fixture = {f['id']: f for f in fixtures}
    for attempt in panel.get('attempts', []):
        key = (attempt.get('fixture_id'), attempt.get('repetition'), attempt.get('arm'))
        entry = {'valid': False}
        checked[key] = entry
        try:
            assert key in expected and actual.count(key) == 1, 'unexpected or duplicated attempt'
            path = Path(attempt['output']) / 'record.json'
            assert sha256(path) == attempt['record_sha256'], 'terminal record hash mismatch'
            record = json.loads(path.read_text())
            assert record == attempt['measurement'], 'cached terminal record differs from raw record'
            assert record['mode'] == ('retained' if key[2].endswith('_retained') else 'fresh')
            if bindings is not None:
                variant = 'candidate' if key[2].startswith('candidate_') else 'released_baseline'
                assert record['binding'] == bindings['variants'][variant], 'wrong adapter/binary binding'
            assert record['status'] == 'executed_unvalidated' and record['actual_exit_code'] == 0
            assert record['shutdown_status'] == 'ok' and record['remaining_process_tree_or_group'] == []
            assert sha256(path.parent / 'stdout') == record['stdout_sha256']
            assert sha256(path.parent / 'stderr') == record['stderr_sha256']
            fixture = by_fixture[key[0]]
            stages = record['revisions']
            assert len(stages) == len(fixture['revisions']), 'missing revision measurements'
            assert [s['revision'] for s in stages] == list(range(len(stages)))
            for index, (stage, revision) in enumerate(zip(stages, fixture['revisions'])):
                worker_path = path.parent / 'session' / f'{index:03}.timing.json'
                assert sha256(worker_path) == stage['worker_timing_sha256']
                worker = json.loads(worker_path.read_text())
                assert stage['worker'] == worker, 'cached sidecar differs from raw sidecar'
                assert worker['revision'] == index and worker['mode'] == record['mode']
                assert stage['path'] == revision['path'] == worker['source']
                assert number(stage['wall_s']), 'invalid or absent measured wall'
                assert stage['status'] == worker['status']
                assert stage['raw_event'] == f"DONE\t{index}\t{worker['status']}\n"
                if revision['expected_valid']:
                    assert worker['status'] == 'executed_unvalidated'
                    assert type(worker['dropped_clauses']) is int and worker['dropped_clauses'] == 0
            # This reparses all taxonomy/rollback files and independent facts.
            # It never consumes attempt['semantic_audit'] pass/status flags.
            fresh_audit = audit({**attempt, 'measurement': record}, fixture)
            assert all(x['passed'] for x in fresh_audit), repr(fresh_audit)
            for revision, answer in zip(fixture['revisions'], fresh_audit):
                if revision['expected_valid'] and answer['semantic']['consistent']:
                    value = answer['semantic']
                    for sub, sup in revision.get('entailed_if_consistent', []):
                        # The public snapshot omits rows with an unsatisfiable
                        # subclass; its explicit unsat verdict entails the row.
                        assert sub in value['unsatisfiable'] or [sub, sup] in value['subsumptions'], 'missing asserted added subsumption'
            calls = sum(s['wall_s'] for s in stages)
            assert number(record['launch_to_ready_wall_s'])
            shutdown = record['shutdown_wall_s']
            assert type(shutdown) in (int, float) and math.isfinite(shutdown) and shutdown >= 0
            total = record['launch_to_ready_wall_s'] + calls + shutdown
            assert number(record['comparable_whole_sequence_wall_s'])
            assert math.isclose(total, record['comparable_whole_sequence_wall_s'], rel_tol=1e-12, abs_tol=1e-9)
            entry.update(valid=True, record=record, semantic_audit=fresh_audit, whole_s=total)
        except Exception as error:
            entry['problem'] = repr(error)
            problems.append({'attempt': list(key), 'problem': repr(error)})
    for fixture in fixtures:
        fid = fixture['id']
        parity = True
        for rep in range(5):
            group = [checked.get((fid, rep, arm), {}) for arm in ARMS]
            if not all(x.get('valid') for x in group):
                parity = False
                continue
            for index, revision in enumerate(fixture['revisions']):
                if revision['expected_valid']:
                    values = [x['semantic_audit'][index]['semantic'] for x in group]
                    if any(v != values[0] for v in values):
                        parity = False
                        problems.append({'fixture': fid, 'repetition': rep, 'revision': index,
                                         'problem': 'raw taxonomy parity differs across arms'})
        rows = []
        for index, revision in enumerate(fixture['revisions']):
            times = {arm: [] for arm in ARMS}
            for rep in range(5):
                for arm in ARMS:
                    entry = checked.get((fid, rep, arm), {})
                    times[arm].append(entry['record']['revisions'][index]['wall_s'] if entry.get('valid') else None)
            ratios = {}
            for name in ('candidate_fresh', 'released_baseline_fresh', 'released_baseline_retained'):
                paired = [a / b if number(a) and number(b) else None
                          for a, b in zip(times['candidate_retained'], times[name])]
                ratios[name] = {'paired_ratios': paired,
                                'median': statistics.median(paired) if all(number(x) for x in paired) else None}
            update = revision['expected_valid'] and revision['operation'] == 'replace'
            ratio = ratios['candidate_fresh']['median']
            passes = parity and ratio is not None and ratio <= 0.8 if update else None
            rows.append({'revision': index, 'label': revision['label'], 'update_threshold_applies': update,
                         'wall_s_by_arm': times, 'candidate_retained_over': ratios,
                         'five_valid_pairs_and_semantic_parity': parity and all(number(x) for x in times['candidate_retained'] + times['candidate_fresh']),
                         'required_ratio_max': 0.8, 'passes': passes})
        whole = {arm: [checked.get((fid, rep, arm), {}).get('whole_s') for rep in range(5)] for arm in ARMS}
        medians = {arm: statistics.median(values) if all(number(v) for v in values) else None for arm, values in whole.items()}
        total_passes = parity and all(medians[x] is not None for x in ARMS)
        total_passes = total_passes and all(medians['candidate_retained'] < medians[x] for x in ('candidate_fresh', 'released_baseline_fresh'))
        summaries.append({'fixture_id': fid, 'all_five_repetitions_raw_semantic_parity': parity,
                          'per_revision': rows, 'whole_sequence': {'walls_by_arm': whole, 'medians_by_arm': medians,
                          'candidate_retained_over_released_retained_median': medians['candidate_retained'] / medians['released_baseline_retained'] if all(number(medians[x]) for x in ('candidate_retained', 'released_baseline_retained')) else None,
                          'includes_init': True, 'passes': total_passes}})
    updates = [row for f in summaries for row in f['per_revision'] if row['update_threshold_applies']]
    passed = bool(updates) and not problems and all(row['passes'] is True for row in updates) and all(f['whole_sequence']['passes'] for f in summaries)
    return {'status': 'pass_provisional_per_case_and_whole_sequence' if passed else 'fail_or_unproven',
            'rule': 'five valid paired repetitions per update, median candidate retained/fresh<=0.8; whole sequence including init below candidate and released fresh medians',
            'reopened_raw_artifacts': True, 'cached_semantic_pass_flags_ignored': True,
            'fixtures': summaries, 'problems': problems,
            'reuse_claim': 'timing acceptance does not convert fallback or stale/absent native counters into retained work'}


def main():
    from run_four_arm import write_json, preflight, resolve_inputs, sha256
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--panel', type=Path, required=True)
    parser.add_argument('--fixtures', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--bindings', type=Path, required=True)
    args = parser.parse_args()
    panel = json.loads(args.panel.read_text())
    bindings = preflight(args.bindings)
    assert panel['binding_sha256'] == sha256(args.bindings)
    assert panel['fixtures_sha256'] == sha256(args.fixtures)
    fixtures = resolve_inputs(json.loads(args.fixtures.read_text()), args.fixtures)
    result = evaluate(panel, fixtures, bindings)
    write_json(args.output, result)
    print(result['status'])


if __name__ == '__main__':
    main()
