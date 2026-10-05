"""Check immutable gold benchmark records against inventory and failure evidence."""
import argparse,collections,hashlib,json,pathlib
parser=argparse.ArgumentParser();parser.add_argument('--partial',action='store_true');args=parser.parse_args()
p=pathlib.Path(__file__).resolve().parent
rows=[json.loads(f.read_text()) for f in (p/'gold-final-admission-53195719').glob('*.owl.json')]
previous={r['ont']:r for r in [json.loads(f.read_text()) for f in (p/'gold-conformance-53193453').glob('*.owl.json')]}
assert len(previous)==592 and len(rows)==len({r['ont'] for r in rows})
assert {r['ont'] for r in rows}<=previous.keys()
if not args.partial: assert {r['ont'] for r in rows}==previous.keys()
invalid={r['ontology']:r for r in json.loads((p/'conformance-inventory-53195475-audit.json').read_text())['results'] if r['status']=='invalid_input'}
failures=[];mismatches=[]
for row in rows:
    assert row['binary_sha256']=='941ca25bb4d58c29d78b57eb44598891da6b06b461b9f5ef99f6ff8a8b987a72'
    assert row['checkpointed'] and row['cpus']==16
    old=previous[row['ont']]
    for key in ['gold_sha256','canonicalizer_sha256','watchdog_sha256','gold_kind']:
        assert row.get(key)==old.get(key),(row['ont'],key)
    if row['status']=='ok':
        if row['verdict'] not in ['match','nogold']: mismatches.append(row)
        if row['verdict']=='match':
            assert not row['consistency_mismatch'] and not row['reported_incomplete']
            assert all(row[k]==0 for k in ['extra','missing','extra_unsat','missing_unsat'])
        continue
    raw=(p/'gold-final-admission-53195719/stderr'/('km_v144__'+row['ont']+'.stderr')).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==row['stderr_sha256']
    text=raw.decode(errors='replace');diagnostic=[line for line in text.splitlines() if line.startswith('invalid OWL 2 DL input')]
    known_invalid=row['rc']==2 and bool(diagnostic) and row['ont'].removesuffix('.owl') in invalid
    failures.append({'ontology':row['ont'],'raw_status':row['status'],'rc':row['rc'],'stderr_hash_verified':True,'verified_invalid_diagnostic':known_invalid,'diagnostic':diagnostic,'tail':None if known_invalid else text[-2000:]})
report={'partial':args.partial,'cases':len(rows),'expected':592,'statuses':dict(collections.Counter(r['status'] for r in rows)),'verdicts':dict(collections.Counter(r['verdict'] for r in rows)),'verified_invalid_diagnostics':sum(r['verified_invalid_diagnostic'] for r in failures),'taxonomy_mismatches':len(mismatches),'failures':failures,'mismatches':mismatches}
name='gold-final-admission-53195719-'+('partial' if args.partial else 'complete')+'-audit.json'
(p/name).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['failures','mismatches']}))
print(json.dumps([r for r in failures if not r['verified_invalid_diagnostic']],indent=2))
