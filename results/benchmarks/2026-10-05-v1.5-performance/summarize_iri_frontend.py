"""Validate frontend-comparison receipts and summarize completed inputs."""
import argparse
import json
from pathlib import Path
from measure_classification import digest


def summarize(directory):
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'full-candidate-inputs.json').read_text())
    inputs = {r['ontology']: r for r in manifest['inputs']}
    seen, errors, unresolved = set(), [], []
    complete_chunks = 0
    for path in sorted((directory / 'chunks').glob('*.json')):
        chunk = json.loads(path.read_text())
        for field, file in [('input_manifest_sha256', 'full-candidate-inputs.json'),
                            ('inventory_sha256', 'iri-cached-full-artifact.json'),
                            ('runner_sha256', 'check_iri_frontend_full.py')]:
            assert chunk[field] == digest(root / file), (path, field)
        assert (chunk['timeout_s_per_arm'], chunk['memory_gib'], chunk['cpus']) == (240, 20, 1)
        task = int(path.stem)
        expected = {r['ontology'] for r in manifest['inputs'][task*32:(task+1)*32]}
        assert len(expected) == 32
        if chunk['status'] == 'complete':
            assert {r['ontology'] for r in chunk['outcomes']} == expected
            complete_chunks += 1
        for row in chunk['outcomes']:
            name = row['ontology']
            assert name in expected and name not in seen
            seen.add(name)
            assert row['source_sha256'] == inputs[name]['sha256']
            assert row['input_admission'] == inputs[name]['input_admission']
            arms = row['arms']
            assert set(arms) == {'original', 'cached'}
            success = all(a['status'] == 'ok' and a['exit_code'] == 0 and a['meta_sha256'] is not None for a in arms.values())
            refusal = all(a['status'] == 'ok' and a['exit_code'] == 3 and a['meta_sha256'] is None for a in arms.values())
            assert row['outcome'] == ('success' if success else ('refusal' if refusal else 'unresolved'))
            terminal = success or refusal
            agrees = terminal and all(arms['original'][k] == arms['cached'][k] for k in ['stdout_sha256', 'stderr_sha256', 'meta_sha256'])
            assert row['exact_agreement'] == agrees
            if not terminal:
                unresolved.append(name)
            elif not agrees:
                errors.append(name)
    return dict(complete=complete_chunks == 60 and len(seen) == 1920,
                complete_chunks=complete_chunks, recorded_inputs=len(seen),
                exact_agreements=len(seen)-len(errors)-len(unresolved),
                differing_results=errors, unresolved=unresolved, release_approved=False,
                diagnostic_only=True, scope='Automatic frontend output and refusal equivalence; not classification.')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    print(json.dumps(summarize(args.directory), indent=2))
