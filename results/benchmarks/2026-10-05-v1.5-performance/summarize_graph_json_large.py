"""Validate and summarize all graph-output diagnostic attempts, including failures."""
import argparse
import json
from pathlib import Path
from statistics import mean, median
from measure_classification import digest

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('directory', type=Path)
a = p.parse_args()
root = Path(__file__).resolve().parent
manifest = root / 'full-candidate-inputs.json'
inventory = root / 'graph-json-artifact.json'
flags = json.loads(inventory.read_text())['flags']
names = ['ore_ont_14459', 'ore_ont_11085', 'ore_ont_8486']
rows, seen, complete = [], set(), set()
for path in sorted((a.directory / 'chunks').glob('*.json')):
    d = json.loads(path.read_text())
    task = int(path.stem)
    assert 0 <= task < 6
    assert d['manifest_sha256'] == digest(manifest)
    assert d['inventory_sha256'] == digest(inventory)
    assert d['runner_sha256'] == digest(root / 'probe_graph_json_large.py')
    assert d['flags'] == flags and d['repetition'] == task % 2
    arms = ['expanded', 'graph'] if task % 2 == 0 else ['graph', 'expanded']
    assert len(d['outcomes']) <= 2
    if d['status'] == 'complete':
        assert len(d['outcomes']) == 2
        complete.add(task)
    for i, row in enumerate(d['outcomes']):
        assert row['ontology'] == names[task // 2]
        assert row['arm'] == arms[i] and row['repetition'] == task % 2
        assert row['graph_edges'] == (row['arm'] == 'graph')
        key = (row['ontology'], row['repetition'], row['arm'])
        assert key not in seen
        seen.add(key)
        if row['verified_solved']:
            assert row['measurement_status'] == 'executed_unvalidated'
            assert row['audit_status'] == 'compared'
            assert row['audit_execution']['status'] == 'ok'
            assert row['audit_execution']['exit_code'] == 0
            assert any(c.get('agreement') is True for c in row['comparisons'].values())
        rows.append(row)
summary = {}
for name in names:
    summary[name] = {}
    for arm in ['expanded', 'graph']:
        selected = [r for r in rows if r['ontology'] == name and r['arm'] == arm]
        verified = [r for r in selected if r['verified_solved']]
        times = [r['wall_s'] for r in verified]
        summary[name][arm] = dict(attempts=len(selected), verified=len(verified),
            mean_wall_s=mean(times) if times else None, median_wall_s=median(times) if times else None,
            output_bytes=[r['taxonomy_bytes'] for r in selected],
            peak_bytes=[r['peak_bytes'] for r in selected])
print(json.dumps(dict(complete=len(complete) == 6, recorded_attempts=len(rows),
    classification_limit_s=240, audit_limit_s=600, memory_gib=20, cpus=1,
    summary=summary, rows=rows, diagnostic_only=True, release_approved=False), indent=2))
