"""Summarize nested diagnostic timers without treating them as additive totals."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def timings(path):
    totals = {name: Counter() for name in ('read_off', 'analysis', 'analyser')}
    counts = Counter()
    for line in path.read_text().splitlines():
        if line.startswith('BRIDGE-READOFF-TIMING '):
            group = 'read_off'
            pairs = re.findall(r'(seed|search|cache|labels)=([0-9.]+)', line)
        elif line.startswith('BRIDGE-ANALYSIS-TIMING '):
            group = 'analysis'
            pairs = re.findall(r'(snapshot|analyse|delivery)=([0-9.]+)', line)
        elif line.startswith('BRIDGE-ANALYSER-PHASE '):
            group = 'analyser'
            pairs = re.findall(r'phase=([a-z-]+) seconds=([0-9.]+)', line)
        else:
            continue
        assert pairs, line
        counts[group] += 1
        for key, value in pairs:
            totals[group][key] += float(value)
    return {'event_counts': dict(counts), 'seconds': {k: dict(v) for k, v in totals.items()}}


def summarize(directory):
    root = Path(__file__).resolve().parent
    inventory_path = root / 'analysis-phase-profile-artifact.json'
    manifest_path = root / 'analysis-phase-profile-inputs.json'
    inventory = json.loads(inventory_path.read_text())
    inputs = {r['ontology']: r for r in json.loads(manifest_path.read_text())['inputs']}
    results = []
    chunks = sorted((directory / 'chunks').glob('*.json'))
    complete = 0
    seen = set()
    for path in chunks:
        chunk = json.loads(path.read_text())
        assert chunk['inventory_sha256'] == digest(inventory_path)
        assert chunk['manifest_sha256'] == digest(manifest_path)
        assert chunk['runner_sha256'] == digest(root / 'profile_analysis_phases.py')
        assert chunk['diagnostic_only'] is True
        assert chunk['flags']['KM_BRIDGE_PHASE_TIMING'] == '1'
        complete += chunk['status'] == 'complete'
        for outcome in chunk['outcomes']:
            name = outcome['ontology']
            assert name not in seen
            seen.add(name)
            output = directory / name
            record_path = output / 'record.json'
            assert digest(record_path) == outcome['measurement_sha256']
            record = json.loads(record_path.read_text())
            assert record['source_sha256'] == inputs[name]['sha256']
            assert record['artifact_sha256'] == inventory['artifacts'][0]['sha256']
            assert (record['timeout_s'], record['memory_mib'], record['cpu_threads']) == (240, 20480, 1)
            assert digest(output / 'stderr') == record['files']['stderr']['sha256']
            assert outcome.get('audit_status') != 'audit_error', outcome
            results.append(dict(outcome, timers=timings(output / 'stderr'),
                                stderr_sha256=record['files']['stderr']['sha256']))
    return dict(diagnostic_only=True, complete=complete == len(inputs) and seen == set(inputs),
                complete_chunks=complete, rows=results, release_approved=False,
                interpretation='Timer groups are nested and must not be added together. '
                'Instrumentation adds I/O. These times cannot establish a release speedup.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = summarize(args.directory)
    with args.output.open('x') as output:
        json.dump(result, output, indent=2)
        output.write('\n')
    print(json.dumps({'complete': result['complete'], 'rows': len(result['rows'])}))
