"""Reconcile final full-output audit with independently verified evidence."""
import hashlib,json,pathlib
v=pathlib.Path(__file__).resolve().parent;p=v.parent
load=lambda f:json.loads(f.read_text())
a=load(v/'full-final-admission-53195718-output-audit.json')
rows={r['ont']:r for r in a['results']}
cases={r['ont']:r for r in load(v/'full-final-admission-53195718-case-records.json')}
prior_cases={r['ont']:r for r in load(v/'full-conformance-53193452-case-records.json')}
prior_audit=load(v/'full-conformance-53193452-output-audit.json')
assert len(rows)==len(cases)==1920 and rows.keys()==cases.keys()==prior_cases.keys()
assert a['summary']['cases']==1920 and prior_audit['summary']['cases']==1920
assert a['summary']['successful_outputs_with_dropped']==0
assert a['summary']['independent_reference_mismatches']==0
assert set(a['summary']['reported_outcomes'])<={'ok','invalid_input','dnf'}
assert all(r['outcome']=='dnf' for r in rows.values() if not r['execution_record_present'])
inv={r['ontology']:r for r in load(v/'conformance-inventory-53195475-audit.json')['results']}
assert {n for n,r in rows.items() if r['reported_outcome']=='invalid_input'}=={n for n,r in inv.items() if r['status']=='invalid_input'}
for n in ['ore_ont_15687','ore_ont_9890']:
    assert rows[n]['outcome']=='ok' and rows[n]['independent_reference_equal'] and rows[n]['independent_source_verified']
references={r['ont']:r for r in load(p/'full-main-lazy-optimized-53175668-difference-adjudication.json')['checks']}
differences=[];new_outputs=[];unchanged=0
for n,r in rows.items():
    if r['outcome']!='ok':continue
    if cases[n]['out_sha256']==prior_cases[n].get('out_sha256') and prior_cases[n]['outcome']=='ok':unchanged+=1
    else:new_outputs.append(n)
    if r.get('consistency_equal') is False or r.get('unsatisfiable_equal') is False or r.get('missing_relations',0)>0 or r.get('extra_relations',0)>0:
        ref=references[n];raw=(p/ref['reference_comparison']).read_bytes()
        assert hashlib.sha256(raw).hexdigest()==ref['comparison_sha256']
        comparison=json.loads(raw);c=comparison.get('candidate',comparison)
        assert c['missing_count']==c['extra_count']==0
        assert not c.get('missing_unsat',[]) and not c.get('extra_unsat',[])
        assert c.get('sha256',c.get('candidate_sha256'))==cases[n]['out_sha256']
        differences.append({'ontology':n,'output_sha256':cases[n]['out_sha256'],'reference_comparison':ref['reference_comparison']})
report={'summary':a['summary'],'all_invalid_refusals_independently_verified':True,'original_two_errors_independently_verified':True,'unchanged_successful_outputs_from_preceding_audited_run':unchanged,'outputs_requiring_further_review':new_outputs,'differences_from_v143_resolved_against_references':differences}
(v/'full-final-admission-53195718-adjudication.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
