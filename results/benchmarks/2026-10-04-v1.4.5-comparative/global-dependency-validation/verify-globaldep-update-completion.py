"""Verify terminal update receipt bindings; no reasoning or taxonomy processing."""
from pathlib import Path
from collections import Counter
import datetime, hashlib, json, subprocess
root=Path('/ibex/scratch/projects/c2014/hohndor/km/v145-comparative-20261004')
accounting=subprocess.check_output(['sacct','-n','-X','-j','53234830','--format=JobID,State,ExitCode','-P'],text=True)
rows=[x.split('|') for x in accounting.splitlines() if x.strip()]
if {x[0] for x in rows}!={f'53234830_{i}' for i in range(20)} or any(x[1:]!=['COMPLETED','0:0'] for x in rows):
    print(json.dumps({'status':'measurement tasks still active or not successfully completed','accounting':accounting}))
    raise SystemExit(0)
selection_path=root/'workload-selection.json'
sources=json.loads(selection_path.read_text())['selected']
assert len(sources)==80 and len({s['ontology'] for s in sources})==80
artifact='a08be6436df9366eb50d823105b3582252f675bd4fa7dde097f5b62d48eedad0'
hashes={}; cold=Counter(); retained=Counter(); revisions=Counter(); source_states=Counter(); failures=[]
def read(p):
    raw=p.read_bytes();hashes[str(p.relative_to(root))]=hashlib.sha256(raw).hexdigest();return json.loads(raw)
for source in sources:
    ont=source['ontology'];base=root/'km-updates-53234830'/ont/'km'
    summary=read(base/'summary.json');prep_path=root/'prepared-updates-53201177'/ont/'receipt.json';prep=read(prep_path)
    assert summary['source_sha256']==prep['source_sha256']==source['sha256']
    source_states[summary['status']]+=1
    if prep['status']!='prepared':
        assert ont=='ore_ont_16744' and prep['status']=='preparation_timeout'
        assert summary['status']=='preparation_or_adapter_error' and not summary['repetitions']
        assert summary['error']=='update preparation failed'
        failures.append({'ontology':ont,'preparation_status':prep['status'],'measurement_status':summary['status']})
        continue
    assert summary['preparation_receipt_sha256']==hashes[str(prep_path.relative_to(root))]
    assert summary['status']=='measurement_complete_requires_semantic_audit'
    assert len(summary['repetitions'])==3
    for rep in range(3):
        summary_rep=summary['repetitions'][rep]
        assert summary_rep['repetition']==rep
        for rev in range(5):
            d=read(base/f'repetition-{rep}/cold/{rev:03}/record.json')
            assert d['artifact_sha256']==artifact and d['source_sha256']==prep['files'][f'{rev:03}.ofn']
            assert d['status'] not in ['running','pending','preparing']
            assert summary_rep['outcomes']['cold'][rev]==d['status']
            cold[d['status']]+=1
        d=read(base/f'repetition-{rep}/retained/record.json')
        assert d['artifact_sha256']==artifact and d['status'] not in ['running','pending','preparing']
        assert summary_rep['outcomes']['retained']==d['status']
        retained[d['status']]+=1
        assert len(d['revisions'])==5
        for rev,item in enumerate(d['revisions']):
            assert item['sha256']==prep['files'][f'{rev:03}.ofn'] and item['revision']==rev
            assert item['status'] not in ['running','pending','preparing']
            revisions[item['status']]+=1
assert sum(cold.values())==1185 and sum(retained.values())==237 and sum(revisions.values())==1185
assert len(failures)==1
out={'observed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'all measurements terminal and bound to source/preparation/candidate; semantic and report reviews separate','candidate_sha256':artifact,'selection_sha256':hashlib.sha256(selection_path.read_bytes()).hexdigest(),'slurm_accounting':accounting,'selected_sources':80,'prepared_sources':79,'preparation_failures':failures,'source_states':dict(source_states),'cold_statuses':dict(cold),'retained_session_statuses':dict(retained),'retained_revision_statuses':dict(revisions),'receipt_hashes':hashes}
with (root/'globaldep-update-measurement-completion.json').open('x') as f:json.dump(out,f,indent=2)
print(json.dumps({k:v for k,v in out.items() if k not in ['receipt_hashes','slurm_accounting']}))
