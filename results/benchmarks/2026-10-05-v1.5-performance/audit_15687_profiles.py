"""Audit every outcome of the pinned same-node 15687 diagnostic."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from compare_taxonomies import compare


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


parser = argparse.ArgumentParser()
for name in ['measurements', 'references', 'output']:
    parser.add_argument('--'+name, type=Path, required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parent
summary = json.loads((args.measurements/'summary.json').read_text())
assert summary['complete'] and len(summary['records']) == 6
assert summary['runner_sha256'] == digest(root/'profile_15687_candidates.py')
assert summary['manifest_sha256'] == digest(root/'full-candidate-inputs.json')
row, = [r for r in json.loads((root/'full-candidate-inputs.json').read_text())['inputs']
        if r['ontology'] == 'ore_ont_15687']
assert summary['input'] == row
assert digest(args.references/'audit.json') == row['reference_audit_sha256']
audit = json.loads((args.references/'audit.json').read_text())
assert audit['source_sha256'] == row['sha256']
records = []
seen = set()
for item in summary['records']:
    key = (item['variant'], item['repeat'])
    assert key not in seen
    seen.add(key)
    inventory_path = root/(item['variant']+'-candidate-artifact.json')
    assert digest(inventory_path) == item['inventory_sha256']
    inventory = json.loads(inventory_path.read_text())
    directory = args.measurements/(str(item['repeat'])+'-'+item['variant'])
    assert digest(directory/'record.json') == item['record_sha256']
    record = json.loads((directory/'record.json').read_text())
    assert record['artifact_sha256'] == inventory['artifacts'][0]['sha256']
    assert record['source_sha256'] == row['sha256']
    assert record['status'] == item['status']
    assert record['timeout_s'] == 240 and record['memory_mib'] == 20480
    result = dict(item, verified=False, comparisons={})
    if record['status'] == 'executed_unvalidated':
        assert digest(directory/'taxonomy.raw') == record['files']['taxonomy.raw']['sha256']
        subprocess.run([sys.executable, str(root/'canonicalize.py'),
            '--input', str(directory/'taxonomy.raw'), '--format', 'km-json',
            '--signature', str(args.references/'signature.tsv'),
            '--output-prefix', str(directory/'canonical'),
            '--fingerprint-script', str(root/'full_iri_fingerprint.py')],
            check=True, capture_output=True, timeout=240)
        answer = json.loads((directory/'canonical.validated.json').read_text())
        for name in ['konclude', 'hermit', 'openllet', 'jfact']:
            previous = audit['outcomes'].get(name, {})
            if previous.get('status') != 'canonicalized_requires_comparison':
                continue
            path = args.references/(name+'.validated.json')
            assert digest(path) == previous['canonical_sha256']
            result['comparisons'][name] = compare(answer, json.loads(path.read_text()))
        result['verified'] = any(v.get('agreement') is True for v in result['comparisons'].values())
        result['canonical_sha256'] = digest(directory/'canonical.validated.json')
    records.append(result)
assert seen == {(v, r) for v in ['data-source', 'work-budget', 'dense-data'] for r in range(2)}
result = dict(diagnostic_only=True, job=53318583, records=records,
              summary_sha256=digest(args.measurements/'summary.json'),
              audit_script_sha256=digest(Path(__file__)),
              full_sweep_timeout_retained=True, release_approved=False,
              scope='Instrumented same-node repeats only. All outcomes retained; these do not replace the frozen full-sweep timeout.')
with args.output.open('x') as out:
    json.dump(result, out, indent=2)
    out.write('\n')
print([(r['variant'], r['repeat'], r['status'], r['verified']) for r in records])
