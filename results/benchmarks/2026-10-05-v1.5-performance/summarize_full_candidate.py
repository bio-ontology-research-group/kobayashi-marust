"""Summarize pinned full-corpus chunks without promoting partial results to acceptance."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
from statistics import mean, median


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def times(rows):
    values = [r['wall_s'] for r in rows if r['verified_solved']]
    return dict(verified_solved=len(values), mean_s=mean(values) if values else None,
                median_s=median(values) if values else None)


def summarize(root, job, baseline_path, variant='native'):
    prefix, inventory, runner, flags = {
        'native': ('full-candidate-', 'native-full-candidate-artifact.json',
                   'run_full_candidate.py', {'KM_HT_DDB': '1', 'KM_HT_NATIVE_FULL': '1'}),
        'conformance': ('conformance-candidate-', 'conformance-candidate-artifact.json',
                        'run_conformance_candidate.py',
                        {'KM_HT_DDB': '1', 'KM_HT_NATIVE_FULL': '1', 'KM_CACHE_CONFORMANCE': '1'}),
        'successor-deadline': ('successor-deadline-candidate-', 'successor-deadline-candidate-artifact.json',
                               'run_successor_deadline_candidate.py',
                               {'KM_HT_DDB': '1', 'KM_HT_NATIVE_FULL': '1',
                                'KM_CACHE_CONFORMANCE': '1', 'KM_HT_SATURATION_BUDGET_CAP_S': '1'}),
        'nominal-guard': ('nominal-guard-candidate-', 'nominal-guard-candidate-artifact.json',
                          'run_nominal_guard_candidate.py',
                          {'KM_HT_DDB': '1', 'KM_HT_NATIVE_FULL': '1', 'KM_CACHE_CONFORMANCE': '1'}),
    }[variant]
    manifest_path = root / 'full-candidate-inputs.json'
    manifest = json.loads(manifest_path.read_text())['inputs']
    expected = {r['ontology']: r for r in manifest}
    assert len(expected) == len(manifest) == 1920
    baseline = json.loads(baseline_path.read_text())['classification']['cases']
    rows = {}
    complete = 0
    for path in sorted((root / (prefix + job) / 'chunks').glob('*.json')):
        chunk = json.loads(path.read_text())
        assert chunk['manifest_sha256'] == digest(manifest_path)
        assert chunk['inventory_sha256'] == digest(root / inventory)
        assert chunk['runner_sha256'] == digest(root / runner)
        assert chunk['flags'] == flags
        index = int(path.stem)
        assert 0 <= index < 60
        expected_chunk = manifest[index * 32:(index + 1) * 32]
        assert len(chunk['outcomes']) <= 32
        if chunk['status'] == 'complete':
            assert len(chunk['outcomes']) == 32
            complete += 1
        for position, row in enumerate(chunk['outcomes']):
            name = row['ontology']
            assert name == expected_chunk[position]['ontology'] and name not in rows
            assert row['input_admission'] == expected[name]['input_admission']
            if row['verified_solved']:
                assert row['input_admission'] == 'checks_passed'
                assert row['measurement_status'] == 'executed_unvalidated'
                assert row['audit_status'] == 'compared'
                assert any(c['agreement'] is True for c in row['comparisons'].values())
            rows[name] = row
    result = dict(job_id=job, variant=variant, complete_chunks=complete, recorded_inputs=len(rows),
                  full_measurement_complete=complete == 60 and len(rows) == 1920,
                  candidate=times(rows.values()), baseline_sha256=digest(baseline_path),
                  status_counts=dict(Counter(r['measurement_status'] for r in rows.values())),
                  audit_errors=[r['ontology'] for r in rows.values() if r.get('audit_status') == 'audit_error'],
                  comparisons={})
    result['status_by_admission'] = {
        admission: dict(Counter(r['measurement_status'] for r in rows.values()
                               if r['input_admission'] == admission))
        for admission in ['checks_passed', 'invalid_input']
    }
    for name in ['km', 'konclude', 'rustdl', 'elk']:
        previous = {r['ontology']: r for r in baseline[name]}
        shared = [r for key, r in rows.items() if r['verified_solved'] and previous.get(key, {}).get('solved')]
        old_times = [previous[r['ontology']]['wall_s'] for r in shared]
        result['comparisons'][name] = dict(
            shared=times(shared), baseline_shared_mean_s=mean(old_times) if old_times else None,
            baseline_shared_median_s=median(old_times) if old_times else None,
            lost_verified=[key for key, r in rows.items() if previous.get(key, {}).get('solved') and not r['verified_solved']],
            gained_verified=[key for key, r in rows.items() if r['verified_solved'] and not previous.get(key, {}).get('solved')])
    result['release_approved'] = False
    result['scope'] = 'Measurement summary only; full correctness review and exact-release certification remain separate.'
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--job', required=True)
    parser.add_argument('--baseline', required=True, type=Path)
    parser.add_argument('--variant', choices=['native', 'conformance', 'nominal-guard', 'successor-deadline'], default='native')
    args = parser.parse_args()
    print(json.dumps(summarize(Path(__file__).resolve().parent, args.job, args.baseline, args.variant), indent=2))
