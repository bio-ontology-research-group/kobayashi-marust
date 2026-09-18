"""Audit the pinned ABox candidate ORE sweep against the released baseline."""
import argparse
import collections
import csv
import json
import math
import statistics
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('root', type=Path)
p.add_argument('baseline', type=Path)
p.add_argument('--binary', required=True)
p.add_argument('--job', required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
names = (a.root / 'ore592.txt').read_text().splitlines()
assert len(names) == len(set(names)) == 592
files = list((a.root / 'full-sweep/results').glob('*.owl.json'))
assert {f.name for f in files} == {n + '.json' for n in names}
semantic = ('status', 'verdict', 'rc', 'consistent', 'reported_incomplete',
            'signature_sha256', 'subsumptions', 'unsatisfiable', 'missing',
            'extra', 'missing_unsat', 'extra_unsat', 'consistency_mismatch')
rows, differences = [], []
for i, name in enumerate(names):
    f = a.root / 'full-sweep/results' / (name + '.json')
    r = json.loads(f.read_text())
    checkpoint = json.loads(Path(str(f) + '.checkpoint.json').read_text())
    assert r == checkpoint, name
    assert r['ont'] == name and r['binary_sha256'] == a.binary, name
    assert r['slurm_array_job_id'] == a.job, name
    assert r['slurm_array_task_id'] == str(i), name
    assert r['cpu_model'] == 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz', name
    assert r['cpus'] == 16 and r['explicit_environment'] == ['KM_ROUTE=auto'], name
    assert r['checkpointed'] and r['selected_route_trace'], name
    assert r['status'] == 'ok' and r['rc'] == 0 and not r['reported_incomplete'], name
    assert r.get('signature_sha256'), name
    assert (a.root / f'slurm-{a.job}_{i}.out').read_text().count('TASK_COMPLETE') == 1, name
    for key in ('wall_s', 'peak_mb'):
        assert isinstance(r[key], (int, float)) and math.isfinite(r[key]) and r[key] > 0, name
    assert r['wall_s'] <= 240 and r['peak_mb'] <= 20480, name
    old = json.loads((a.baseline / (name + '.json')).read_text())
    changed = {k: [old.get(k), r.get(k)] for k in semantic if old.get(k) != r.get(k)}
    if changed:
        differences.append({'ont': name, 'differences': changed})
    rows.append(r)
assert not differences, differences
summary = {
    'binary_sha256': a.binary, 'job': a.job,
    'results': len(rows), 'checkpoints': len(rows), 'completion_markers': len(rows),
    'status': dict(collections.Counter(r['status'] for r in rows)),
    'verdict': dict(collections.Counter(r['verdict'] for r in rows)),
    'semantic_differences': differences,
    'metrics_population': 'All 592 completed runs; includes two without retained external gold',
    'metrics': {f'{agg}_{key}': fn(r[key] for r in rows)
                for agg, fn in [('mean', statistics.mean), ('median', statistics.median)]
                for key in ['wall_s', 'peak_mb']},
}
a.output.mkdir(parents=True, exist_ok=True)
(a.output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
with (a.output / 'per-ontology.tsv').open('w') as f:
    fields = ['ont', 'status', 'verdict', 'wall_s', 'peak_mb', 'selected_route_trace',
              'signature_sha256', 'binary_sha256']
    w = csv.DictWriter(f, fields, delimiter='\t', lineterminator='\n', extrasaction='ignore')
    w.writeheader()
    w.writerows(rows)
print(json.dumps(summary, indent=2))
