#!/usr/bin/env python3
"""Recover the reporting tail only; never invoke a reasoner or overwrite measurements."""
import json, os, sys, hashlib
from pathlib import Path
D=Path('/ibex/project/c2014/hohndor/km/v151-incremental-20261014/validation/full80-monitor-scope-v1')
sys.path.insert(0,str(D))
import run_shard as driver
from evaluate_public_owlapi_digest import evaluate
sha=driver.sha256
idx=int(os.environ['SLURM_ARRAY_TASK_ID']); case,rep=divmod(idx,5)
out=D/'shards'/f'task-{case:03}-rep-{rep}'
p=out/'panel.json'
top=json.loads(p.read_text())
assert top['status']=='running' and len(top['attempts'])==4
log=D/f'slurm-54101937_{idx}.log'
assert "ModuleNotFoundError: No module named 'evaluate_public_owlapi_digest'" in log.read_text()
assert sha(D/'run_shard.py')==top['driver_sha256']
bind=D/'four-arm-bindings.json'
assert sha(bind)==top['binding_sha256']
inv=driver.preflight(bind)
fp=D.parent/'full80-11db48ce-v1'/'fixtures'/f'task-{case:03}.json'
assert sha(fp)==top['fixtures_sha256']
fixtures=driver.resolve_inputs(json.loads(fp.read_text()),fp)
assert len(fixtures)==1
f=fixtures[0]
assert all(sha(r['path'])==r['sha256'] for r in f['revisions'])
assert sha(D.parents[1]/'final-runtime-v2'/'control'/'acceptance-protocol.json')==top['protocol_sha256']
assert [a['arm'] for a in top['attempts']]==list(driver.ORDERS[rep])
complete=True
for a in top['attempts']:
 rp=Path(a['output'])/'record.json'
 assert sha(rp)==a['record_sha256']
 assert json.loads(rp.read_text())==a['measurement']
 assert driver.audit(a,f)==a['semantic_audit']
 assert driver.cleanup_is_proven_empty(a['measurement']) and a['cleanup_proven_empty']
 complete &= a['measurement']['status']=='executed_unvalidated' and all(x['passed'] for x in a['semantic_audit'])
for i,r in enumerate(f['revisions']):
 if r['expected_valid']:
  values=[a['semantic_audit'][i].get('semantic_identity') for a in top['attempts']]
  complete &= values[0] is not None and all(v==values[0] for v in values)
top['fixture_summaries']=[{'fixture_id':f['id'],**driver.summarize(f,top['attempts'],top['repetitions'])}]
top.update(status='complete_execution_and_parity' if complete else 'completed_with_failures',postflight_pins_identical=True)
top['performance_acceptance']=evaluate(top,fixtures,inv)
original=p.read_bytes()
backup=out/'panel.before-reporting-recovery.json'
with backup.open('xb') as stream: stream.write(original)
receipt={'schema':'reporting-only-recovery-v1','original_panel_sha256':hashlib.sha256(original).hexdigest(),'original_error_log_sha256':sha(log),'recovery_script_sha256':sha(__file__),'evaluator_sha256':sha(D/'runtime/owlapi-runner/cleanup-evidence-v3.2-digest/evaluate_public_owlapi_digest.py'),'raw_measurements_recomputed':False,'raw_record_hashes':[a['record_sha256'] for a in top['attempts']]}
tmp=out/'panel.recovered.tmp'
driver.write_json(tmp,top)
receipt['recovered_panel_sha256']=sha(tmp)
driver.write_json(out/'reporting-recovery.json',receipt)
tmp.replace(p)
print(json.dumps(receipt))
