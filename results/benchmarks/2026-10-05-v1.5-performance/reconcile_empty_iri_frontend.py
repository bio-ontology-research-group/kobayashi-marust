"""Reconcile complete frozen frontend, invalid-refusal, and clause-order audits."""
import argparse
from collections import Counter
import json
from pathlib import Path
from check_empty_iri_frontend import digest

parser = argparse.ArgumentParser()
parser.add_argument('--frontend', type=Path, required=True)
parser.add_argument('--refusals', type=Path, required=True)
parser.add_argument('--clause-order', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--large', type=Path, required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parent
manifest_path = root / 'full-candidate-inputs.json'
manifest = json.loads(manifest_path.read_text())
artifact_hash = digest(root / 'empty-iri-frontend-artifacts.json')
artifacts = json.loads((root / 'empty-iri-frontend-artifacts.json').read_text())

def chunks(directory, count, checker):
    rows, hashes = [], {}
    for task in range(count):
        path = directory / 'chunks' / (str(task) + '.json')
        data = json.loads(path.read_text())
        assert data['status'] == 'complete', (directory, task, 'incomplete')
        assert data['manifest_sha256'] == digest(manifest_path)
        assert data['artifact_manifest_sha256'] == artifact_hash
        assert data['checker_sha256'] == digest(root / checker)
        hashes[str(task)] = digest(path)
        rows.extend(data['outcomes'])
    assert len({r['ontology'] for r in rows}) == len(rows)
    return rows, hashes

main, main_hashes = chunks(args.frontend, 60, 'check_empty_iri_frontend.py')
refused, refused_hashes = chunks(args.refusals, 7, 'check_empty_iri_refusals.py')
large, large_hashes = chunks(args.large, 1, 'check_empty_iri_frontend.py')
assert [r['ontology'] for r in large] == ['ore_ont_15687']
large = {r['ontology']:r for r in large}
assert [r['ontology'] for r in main] == [r['ontology'] for r in manifest['inputs']]
invalid = [r for r in manifest['inputs'] if r['input_admission'] == 'invalid_input']
assert [r['ontology'] for r in refused] == [r['ontology'] for r in invalid]
assert [r['source_sha256'] for r in main] == [r['sha256'] for r in manifest['inputs']]
assert [r['source_sha256'] for r in refused] == [r['sha256'] for r in invalid]
order = json.loads((args.clause_order / 'summary.json').read_text())
assert order['status'] == 'complete'
assert order['manifest_sha256'] == digest(manifest_path)
assert order['source_chunks'] == main_hashes
assert order['checker_sha256'] == digest(root / 'compare_frontend_clause_multiset.py')
selected = [r['ontology'] for r, source in zip(main, manifest['inputs'])
            if not r['passed'] and source['input_admission'] == 'checks_passed']
assert order['selected'] == selected
assert [r['ontology'] for r in order['outcomes']] == selected
refused = {r['ontology']:r for r in refused}
reordered = {r['ontology']:r for r in order['outcomes']}
results = []
for row, source in zip(main, manifest['inputs']):
    name = row['ontology']
    if row['passed']:
        proof = args.frontend / name / 'receipt.json'
        assert digest(proof) == row['receipt_sha256']
        data = json.loads(proof.read_text())
        assert data['old_binary_sha256'] == artifacts['old']['sha256']
        assert data['new_binary_sha256'] == artifacts['new']['sha256']
        assert len(data['rows']) == 1
        assert data['rows'][0]['source_sha256'] == source['sha256']
        assert data['rows'][0]['equal_after_source_bound_renaming']
        status = 'byte_identical' if row['byte_identical'] else 'source_bound_renaming'
    elif source['input_admission'] == 'invalid_input' and refused[name]['passed']:
        proof = args.refusals / name / 'receipt.json'
        assert digest(proof) == refused[name]['receipt_sha256']
        data = json.loads(proof.read_text())
        assert data['old_binary_sha256'] == artifacts['old']['sha256']
        assert data['new_binary_sha256'] == artifacts['new']['sha256']
        assert data['rows'][0]['source_sha256'] == source['sha256']
        assert data['rows'][0]['same_frontend_outcome']
        status = ('identical_invalid_input_refusal' if data['rows'][0]['same_refusal']
                  else 'identical_frontend_on_invalid_input')
    elif name in reordered and reordered[name]['passed']:
        assert reordered[name]['source_sha256'] == source['sha256']
        proof = args.clause_order / (name + '.json')
        assert digest(proof) == reordered[name]['receipt_sha256']
        status = 'source_bound_renaming_and_clause_order'
    elif name in large and large[name]['passed']:
        assert row['execution_status'] == 'memout'
        proof = args.large / name / 'receipt.json'
        assert digest(proof) == large[name]['receipt_sha256']
        data = json.loads(proof.read_text())
        assert data['old_binary_sha256'] == artifacts['old']['sha256']
        assert data['new_binary_sha256'] == artifacts['new']['sha256']
        assert data['rows'][0]['source_sha256'] == source['sha256']
        assert data['rows'][0]['equal_after_source_bound_renaming']
        status = 'preserved_with_larger_validation_memory'
    else:
        status = 'unresolved'
    results.append(dict(ontology=name, source_sha256=source['sha256'], status=status))
assert len(results) == 1920
summary = dict(frontend_preservation_passed=all(r['status'] != 'unresolved' for r in results),
               input_count=len(results), status_counts=dict(Counter(r['status'] for r in results)),
               manifest_sha256=digest(manifest_path), artifact_manifest_sha256=artifact_hash,
               main_chunk_sha256=main_hashes, refusal_chunk_sha256=refused_hashes,
               larger_validation_chunk_sha256=large_hashes,
               clause_order_summary_sha256=digest(args.clause_order / 'summary.json'),
               runner_sha256=digest(__file__), outcomes=results, release_approved=False,
               scope='Frontend preservation only; full classification and runtime acceptance remain required.')
assert not args.output.exists(), 'Do not overwrite a previous reconciliation'
args.output.write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k:summary[k] for k in ['frontend_preservation_passed','input_count','status_counts']}))
