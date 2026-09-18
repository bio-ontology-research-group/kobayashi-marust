import copy,json,tempfile,unittest
from pathlib import Path
import justification_corrections as c
import render_justification_comparison as report

class Corrections(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory(dir=Path.cwd()/".work/inputs");self.root=Path(self.tmp.name)
  self.originals=[];self.corrected=[]
  for final in [False,True]:
   label='final' if final else 'baseline';root=self.root/label;root.mkdir()
   binary=root/'km.ibex';binary.write_text(label)
   original=self.make_source(root,label,binary,final)
   corrected=self.make_source(self.root/(label+'-fixed'),label+'-fixed',binary,final,original)
   self.originals.append(original);self.corrected.append(corrected)
 def tearDown(self):self.tmp.cleanup()
 def make_source(self,root,label,binary,final,original=None,arm='km-common'):
  root.mkdir(exist_ok=True);(root/'tasks').mkdir()
  java=root/'JustificationBenchmark.java';java.write_text('prefix\n'+(c.NEW if original else c.OLD)+'\nsuffix\n')
  runner=root/'justification_run.py';runner.write_text('unchanged runner')
  jar=root/'classifier-hermit.jar';jar.write_text('unchanged runtime')
  manifest={str(p):c.digest(p) for p in [java,runner,jar,binary]}
  mp=root/'driver-manifest.json';mp.write_text(json.dumps(manifest));(root/'task-count.txt').write_text('6')
  for rep in range(6):
   t=dict(ontology='fixture',query_id='q000',query_hash='query',track='module',repetition=rep,warmup=rep==0,sha256='input',sub='a',super='b',input='frozen.ofn',el=True,limits=[1,10,100],km=str(binary),classes=str(root/'classes'),konclude=str(root/'konclude'),driver_manifest=str(mp),driver_manifest_sha256=c.digest(mp),arms=['km-native','km-common']+([] if final else ['hermit-common','konclude-common']))
   if original:
    op=Path(original['spec']['manifest_root'])/'tasks'/('%04d.json'%rep);old=json.loads(op.read_text())
    t.update(arms=[arm],harness_revision='stream-v4',prior_task_sha256=c.digest(op),prior_driver_manifest_sha256=old['driver_manifest_sha256'])
   (root/'tasks'/('%04d.json'%rep)).write_text(json.dumps(t))
  spec=dict(label=label,manifest_root=str(root),results_root=str(root/'results'))
  if original:spec.update(replaces=original['spec']['label'],correction_arm=arm)
  return dict(spec=spec,manifest=manifest)
 def test_exact_fix_accepted(self):
  self.assertEqual(c.validate(self.originals[0],self.corrected[0]),[])
 def test_implicit_legacy_arms_accepted(self):
  oldroot=Path(self.originals[0]['spec']['manifest_root'])
  newroot=Path(self.corrected[0]['spec']['manifest_root'])
  for p in (oldroot/'tasks').glob('*.json'):
   t=json.loads(p.read_text());del t['arms'];p.write_text(json.dumps(t))
   np=newroot/'tasks'/p.name;nt=json.loads(np.read_text());nt['prior_task_sha256']=c.digest(p);np.write_text(json.dumps(nt))
  self.assertEqual(c.validate(self.originals[0],self.corrected[0]),[])
  self.assertIn('konclude-common',c.arms(t))
 def test_missing_task_rejected(self):
  (Path(self.corrected[0]['spec']['manifest_root'])/'tasks/0000.json').unlink()
  self.assertTrue(c.validate(self.originals[0],self.corrected[0]))
 def test_query_change_rejected(self):
  p=Path(self.corrected[0]['spec']['manifest_root'])/'tasks/0000.json';t=json.loads(p.read_text());t['sub']='other';p.write_text(json.dumps(t))
  self.assertTrue(c.validate(self.originals[0],self.corrected[0]))
 def test_unrelated_adapter_edit_rejected_even_with_rehashed_manifest(self):
  source=self.corrected[0];p=Path(source['spec']['manifest_root'])/'JustificationBenchmark.java';p.write_text(p.read_text()+'alter query\n');source['manifest'][str(p)]=c.digest(p)
  self.assertTrue(c.validate(self.originals[0],source))
 def test_runtime_change_rejected(self):
  source=self.corrected[0];k=next(k for k in source['manifest'] if k.endswith('classifier-hermit.jar'));source['manifest'][k]='changed'
  self.assertTrue(c.validate(self.originals[0],source))
 def konclude_correction(self):
  original=self.originals[0]
  binary=Path(next(k for k in original['manifest'] if k.endswith('km.ibex')))
  return self.make_source(self.root/'konclude-fixed','konclude-fixed',binary,False,original,'konclude-common')
 def test_disjoint_corrections_accepted_and_selected_without_fallback(self):
  correction=self.konclude_correction()
  self.assertEqual(c.validate(self.originals[0],correction),[])
  cfg=dict(sources=[self.originals[0]['spec']],km_final_sources=[self.originals[1]['spec']],common_corrections=[s['spec'] for s in self.corrected+[correction]],expected_baseline_tasks=6,validation_only=True)
  out=self.root/'disjoint-report';r=report.render(cfg,out)
  self.assertEqual(r['integrity_issues'],[])
  self.assertEqual(r['attempts'],162);self.assertEqual(r['comparison_selected_attempts'],108)
  import csv
  with (out/'paired-wall.tsv').open() as stream:pairs=list(csv.DictReader(stream,delimiter='\t'))
  peers=[x for x in pairs if x['peer_arm']=='konclude-common']
  self.assertEqual(len(peers),30)
  self.assertTrue(all(x['peer_source']=='konclude-fixed' and x['paired_eligible']=='False' for x in peers))
 def test_overlapping_corrections_rejected(self):
  cfg=dict(sources=[self.originals[0]['spec']],km_final_sources=[self.originals[1]['spec']],common_corrections=[s['spec'] for s in self.corrected]+[self.corrected[0]['spec']],expected_baseline_tasks=6,validation_only=True)
  r=report.render(cfg,self.root/'overlap-report')
  self.assertTrue(any('duplicate correction target' in i['detail'] for i in r['integrity_issues']))
 def test_absent_original_arm_rejected(self):
  self.corrected[1]['spec']['correction_arm']='konclude-common'
  self.assertTrue(any('absent from original' in i for i in c.validate(self.originals[1],self.corrected[1])))
 def test_missing_peer_panel_rejected(self):
  correction=self.konclude_correction()
  binary=Path(next(k for k in self.originals[0]['manifest'] if k.endswith('km.ibex')))
  other=self.make_source(self.root/'other','other',binary,False)
  cfg=dict(sources=[self.originals[0]['spec'],other['spec']],common_corrections=[correction['spec']],expected_baseline_tasks=6,validation_only=True)
  r=report.render(cfg,self.root/'missing-panel-report')
  self.assertTrue(any('every original panel' in i['detail'] for i in r['integrity_issues']))
 def test_full_render_preserves_archive_without_failure_fallback(self):
  cfg=dict(sources=[self.originals[0]['spec']],km_final_sources=[self.originals[1]['spec']],common_corrections=[s['spec'] for s in self.corrected],expected_baseline_tasks=6,validation_only=True)
  out=self.root/'report';r=report.render(cfg,out)
  self.assertEqual(r['integrity_issues'],[])
  self.assertEqual(r['attempts'],144);self.assertEqual(r['comparison_selected_attempts'],108)
  self.assertFalse(r['matrix_execution_complete'])
  import csv
  with (out/'attempts.tsv').open() as stream:rows=list(csv.DictReader(stream,delimiter='\t'))
  old=[x for x in rows if x['arm']=='km-common' and x['harness_revision']=='original-v3'];self.assertEqual(len(old),36)
  self.assertTrue(all(x['comparison_selected']=='False' for x in old))
  with (out/'paired-wall.tsv').open() as stream:pairs=list(csv.DictReader(stream,delimiter='\t'))
  common=[x for x in pairs if x['km_arm']=='km-common'];self.assertEqual(len(common),30)
  self.assertTrue(all(x['km_source']=='final-fixed' and x['paired_eligible']=='False' for x in common))

if __name__=='__main__':unittest.main()
