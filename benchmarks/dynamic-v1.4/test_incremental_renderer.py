import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('renderer',HERE/'render_incremental_comparison.py')
renderer=importlib.util.module_from_spec(spec);spec.loader.exec_module(renderer)


def arm(reasoner, wall=2, digest='a'*64, status='ok'):
 return {'complete':status=='ok','status':status,'issues':[], 'states':{'0':{'sha256':digest,'issues':[]}},
  'measurement':{'status':status,'rc':0,'wall_s':wall,'peak_mib':10,'completed_states':1,'slurm_job':'123','runtime_sha256':reasoner},
  'timings':{'intervals':{'inference_s':{'initial_s':1,'update_sum_s':wall,'total_s':wall}}}}

def fixture():
 arms={r+'/'+a:arm(r,4 if a=='fresh' else 2) for r in ('hermit','jfact','km') for a in ('session','fresh')}
 return {'phase':'panel-pilot','cases':{'mfomd-n1':{'expected_states':1,'manifest_sha256':'m','repetitions':{'0':{'arms':arms}}}},'summary':{'expected_arms':6}}

class RendererTests(unittest.TestCase):
 def setUp(self):
  tmp=HERE.parents[1]/'.work/tmp';tmp.mkdir(parents=True,exist_ok=True)
  self.temp=tempfile.TemporaryDirectory(dir=tmp);self.root=Path(self.temp.name)
 def tearDown(self):self.temp.cleanup()
 def render(self,audits,receipts=()):
  specs=[]
  for label,a in audits:
   p=self.root/(label+'.json');p.write_text(json.dumps(a));specs.append(label+'='+str(p))
  return renderer.render(specs,self.root/'result',receipts)
 def test_complete_but_incorrect_pair_never_has_speedup(self):
  a=fixture()
  for k in ('km/session','km/fresh'):a['cases']['mfomd-n1']['repetitions']['0']['arms'][k]['states']['0']['sha256']='b'*64
  rows,summaries,ratios,report=self.render([('baseline',a)])
  self.assertTrue(report['coverage'][0]['execution_complete'])
  self.assertEqual([r['verdict'] for r in rows if r['reasoner']=='km'],['incorrect','incorrect'])
  self.assertFalse(any(r['reasoner']=='km' for r in ratios))
 def test_reference_disagreement_cannot_be_hidden(self):
  a=fixture();a['cases']['mfomd-n1']['repetitions']['0']['arms']['jfact/fresh']['states']['0']['sha256']='b'*64
  rows,_,ratios,_=self.render([('baseline',a)])
  self.assertFalse(any(r['correct_complete'] for r in rows));self.assertEqual(ratios,[])
 def test_warmup_excluded_and_five_repetition_denominator_kept(self):
  a=fixture();a['phase']='measured';case=a['cases']['mfomd-n1'];case['repetitions']['warmup']=copy.deepcopy(case['repetitions']['0'])
  for arm in case['repetitions']['warmup']['arms'].values():arm['measurement']['wall_s']=10000
  a['summary']['expected_arms']=12
  rows,summaries,ratios,report=self.render([('baseline',a)])
  self.assertTrue(all(s['planned_attempts']==5 for s in summaries))
  self.assertTrue(all(s['correct_wall_max_s']<=4 for s in summaries))
  self.assertTrue(all(r['repetition']!='warmup' for r in ratios))
  self.assertEqual(report['coverage'][0]['planned_attempts'],36)
  self.assertFalse(report['coverage'][0]['execution_complete'])
 def test_km_only_candidate_uses_exact_manifest_reference(self):
  a=fixture();candidate=copy.deepcopy(a);arms=candidate['cases']['mfomd-n1']['repetitions']['0']['arms'];candidate['cases']['mfomd-n1']['repetitions']['0']['arms']={k:v for k,v in arms.items() if k.startswith('km/')};candidate['summary']['expected_arms']=2
  rows,_,_,_=self.render([('baseline',a),('candidate',candidate)])
  self.assertTrue(all(r['correct_complete'] for r in rows if r['label']=='candidate'))
 def test_changed_manifest_blocks_borrowed_reference(self):
  a=fixture();candidate=copy.deepcopy(a);case=candidate['cases']['mfomd-n1'];case['manifest_sha256']='different';case['repetitions']['0']['arms']={'km/fresh':arm('km')};candidate['summary']['expected_arms']=1
  rows,_,_,_=self.render([('baseline',a),('candidate',candidate)])
  self.assertFalse(next(r for r in rows if r['label']=='candidate')['correct_complete'])
 def test_stale_timeout_requires_scheduler_terminal_receipt(self):
  a=fixture();m=a['cases']['mfomd-n1']['repetitions']['0']['arms']['km/session'];m['status']='timeout';m['complete']=False;m['measurement'].pop('rc')
  rows,_,_,report=self.render([('baseline',a)])
  self.assertFalse(next(r for r in rows if r['reasoner']=='km' and r['arm']=='session')['terminal'])
  self.assertFalse(report['coverage'][0]['execution_complete'])
 def test_scheduler_termination_does_not_prove_correctness(self):
  a=fixture();m=a['cases']['mfomd-n1']['repetitions']['0']['arms']['km/session'];m['status']='running';m['complete']=False;m['measurement'].pop('rc')
  p=self.root/'scheduler.tsv';p.write_text('JobID\tState\tExitCode\n123\tTIMEOUT\t0:15\n')
  rows,_,_,report=self.render([('baseline',a)],[p]);row=next(r for r in rows if r['reasoner']=='km' and r['arm']=='session')
  self.assertTrue(row['terminal']);self.assertFalse(row['correct_complete']);self.assertEqual(row['operational_status'],'timeout')
  self.assertTrue(report['coverage'][0]['execution_complete'])

 def test_failure_sidecar_preserves_raw_status(self):
  a=fixture();d=a['cases']['mfomd-n1']['repetitions']['0']['arms']['km/session'];d['status']='error';d['complete']=False
  audit=self.root/'baseline.json';audit.write_text(json.dumps(a))
  sidecar=self.root/'cause.json';sidecar.write_text(json.dumps({'entries':[{'label':'baseline','audit_sha256':renderer.sha(audit),'case':'mfomd-n1','repetition':'0','reasoner':'km','arm':'session','measurement_sha256':'','reported_status':'error','classification':'timeout','findings':[{'kind':'timeout','evidence':{'path':'bound-state.json'},'excerpt':'status=timeout'}]}]}))
  rows,_,_,_=renderer.render(['baseline='+str(audit)],self.root/'result',failure_paths=[sidecar])
  row=next(r for r in rows if r['reasoner']=='km' and r['arm']=='session')
  self.assertEqual(row['raw_status'],'error');self.assertEqual(row['operational_status'],'error');self.assertEqual(row['verdict'],'timeout')
  self.assertEqual(row['failure_sidecar_sha256'],renderer.sha(sidecar));self.assertFalse(row['correct_complete'])

if __name__=='__main__':unittest.main()
