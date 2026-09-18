import csv, hashlib, json, math
from collections import Counter, defaultdict
from pathlib import Path

root = Path('.work/artifacts/incremental-final-comparison')
report = root / 'comparison'
paths = [Path('.work/artifacts/incremental-original-final-audit/main-audit.json'),
         Path('.work/artifacts/incremental-supplementary-final-audit/main-audit.json'),
         Path('.work/artifacts/incremental-v141-final-audit/main-audit.json')]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
meta = json.loads((report / 'report.json').read_text())
assert [sha(p) for p in paths] == [x['sha256'] for x in meta['inputs']]
assert sha(root / 'render_incremental_comparison.py') == meta['renderer_sha256']
for key in ('failure_sidecars', 'scheduler_receipts'):
    for item in meta[key]: assert sha(root / Path(item['path']).name) == item['sha256']
attempts = {}; refs = defaultdict(lambda: defaultdict(set)); partial_mismatches = []
for idx, path in enumerate(paths):
    audit = json.loads(path.read_text()); label = meta['inputs'][idx]['label']; audit_hash = sha(path)
    expected_cases = ({f'{o}-n{n}' for o in ('mmo','hao','vto','mfomd','to','uberon') for n in (1,10,100)}
                      if idx == 0 else {f'{o}-n{n}' for o in (('zfa','mro') if idx == 1 else ('mmo','hao','vto','mfomd','to','uberon','zfa','mro')) for n in (1,10,100)})
    assert set(audit['cases']) == expected_cases
    statuses = Counter()
    for case, c in audit['cases'].items():
        assert c['expected_states'] == 251
        assert set(c['repetitions']) == {'warmup','0','1','2','3','4'}
        reasoners = ('km',) if idx == 2 else ('km','hermit','jfact','openllet') + (('elk','whelk') if case.split('-')[0] in ('mmo','hao','vto') else ())
        arms = {f'{r}/{a}' for r in reasoners for a in ('session','fresh')}
        if idx != 2: arms.add('konclude/fresh')
        for rep, rr in c['repetitions'].items():
            assert set(rr['arms']) == arms
            for arm, a in rr['arms'].items():
                m = a['measurement']; statuses[a['status']] += 1
                assert m['manifest_sha256'] == c['manifest_sha256']
                assert (m['history_timeout_s'],m['state_timeout_s'],m['memcap_mib']) == (7200,240,20480)
                assert 'rc' in m and m['rc'] is not None
                assert m['completed_states'] == len(a['states'])
                if a['complete']: assert len(a['states']) == 251 and not a['issues']
                v = None
                if a['complete'] and set(a['states']) == set(map(str,range(251))):
                    assert all(not s['issues'] and len(s['sha256']) == 64 for s in a['states'].values())
                    v = tuple(a['states'][str(i)]['sha256'] for i in range(251))
                key = (label,case,rep,*arm.split('/')); assert key not in attempts
                attempts[key] = (a,m,c['manifest_sha256'],v,audit_hash)
                if arm in ('hermit/fresh','jfact/fresh') and v:
                    refs[(case,c['manifest_sha256'])][arm].add(v)
            if idx != 2:
                for arm,a in rr['arms'].items():
                    for ref in ('hermit/fresh','jfact/fresh'):
                        b = rr['arms'][ref]
                        for rev in a['states'].keys() & b['states'].keys():
                            if a['states'][rev]['sha256'] != b['states'][rev]['sha256']:
                                partial_mismatches.append([case,rep,arm,ref,rev])
    assert dict(statuses) == audit['summary']['measurement_statuses']
oracle = {}
for key, r in refs.items():
    all_vectors = r['hermit/fresh'] | r['jfact/fresh']
    if r['hermit/fresh'] and r['jfact/fresh'] and len(all_vectors) == 1:
        oracle[key] = next(iter(all_vectors))
rows = list(csv.DictReader((report/'attempts.tsv').open(),delimiter='\t'))
assert len(rows) == len(attempts) == 1800
seen = {}; measured = Counter()
for row in rows:
    key = tuple(row[k] for k in ('label','case','repetition','reasoner','arm'))
    assert key not in seen; seen[key] = row
    a,m,manifest,v,h = attempts[key]
    assert row['audit_sha256'] == h and row['manifest_sha256'] == manifest
    assert row['measurement_sha256'] == a['measurement_sha256']
    assert row['runtime_sha256'] == m['runtime_sha256']
    correct = v is not None and (key[1],manifest) in oracle and v == oracle[(key[1],manifest)] and a['status'] == 'ok'
    assert (row['correct_complete']=='True') == correct
    assert row['warmup'] == str(key[2]=='warmup')
    assert row['terminal'] == 'True'
    if key[2]!='warmup': measured[(key[0],row['verdict'])] += 1
paired = list(csv.DictReader((report/'paired-speedups.tsv').open(),delimiter='\t'))
for row in paired:
    key = tuple(row[k] for k in ('label','case','repetition','reasoner'))
    assert key[2] != 'warmup'
    for arm in ('session','fresh'): assert seen[key+(arm,)]['correct_complete']=='True'
    assert math.isclose(float(row['fresh_over_session']),float(row['fresh_s'])/float(row['session_s']),rel_tol=1e-12)
out = dict(status='pass',attempts=len(rows),paired_rows=len(paired),oracle_histories=len(oracle),
           measured_verdicts={':'.join(k):v for k,v in measured.items()},
           available_state_digest_mismatches=partial_mismatches,
           report_sha256=sha(report/'report.json'),verifier_sha256=sha(Path(__file__)))
(root/'parent-comparison-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k != 'available_state_digest_mismatches'}))
print('Available-state mismatches:',len(partial_mismatches))
