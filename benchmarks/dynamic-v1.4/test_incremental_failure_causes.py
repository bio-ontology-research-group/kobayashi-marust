import importlib.util
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('failure_causes',HERE/'enrich_incremental_failures.py')
causes=importlib.util.module_from_spec(spec);spec.loader.exec_module(causes)

class FailureCauseTests(unittest.TestCase):
 def setUp(self):
  tmp=HERE.parents[1]/'.work/tmp';tmp.mkdir(parents=True,exist_ok=True)
  self.temp=tempfile.TemporaryDirectory(dir=tmp);self.root=Path(self.temp.name)
  self.measurement={'rc':1,'runtime_sha256':'b'*64,'completed_states':0,'expected_states':251}
  raw=json.dumps(self.measurement).encode();(self.root/'measurement.json').write_bytes(raw)
  self.arm={'status':'error','path':str(self.root),'measurement':self.measurement,'measurement_sha256':hashlib.sha256(raw).hexdigest()}
 def tearDown(self):self.temp.cleanup()
 def state(self,status):
  (self.root/'000.json').write_text(json.dumps({'revision':0,'reasoner':'konclude','arm':'fresh','binary_sha256':'b'*64,'status':status}))
 def test_explicit_timeout_over_generic_supervisor_error(self):
  self.state('timeout');r=causes.inspect_failure(self.arm,'konclude')
  self.assertEqual(r['reported_status'],'error');self.assertEqual(r['classification'],'timeout')
 def test_parser_rejection_is_not_speculatively_unsupported(self):
  self.state('output_error');(self.root/'000.response.xml').write_text('<Response><Error><ErrorText>OWL2/Functional ontology parsing error: Expecting close delimiter but got Class.</ErrorText></Error></Response>')
  self.assertEqual(causes.inspect_failure(self.arm,'konclude')['classification'],'parse_error')
 def test_unsupported_exception_is_explicit(self):
  (self.root/'driver.stderr').write_text('java.lang.UnsupportedOperationException: axiom type\n')
  self.assertEqual(causes.inspect_failure(self.arm,'jfact')['classification'],'unsupported')
 def test_plain_error_and_missing_evidence_not_guessed(self):
  (self.root/'driver.stderr').write_text('worker exited -1\n')
  self.assertEqual(causes.inspect_failure(self.arm,'km')['classification'],'missing_evidence')
  (self.root/'driver.stderr').unlink()
  self.assertEqual(causes.inspect_failure(self.arm,'km')['classification'],'missing_evidence')
 def test_conflicting_direct_evidence_remains_ambiguous(self):
  self.state('timeout');(self.root/'driver.stderr').write_text('java.lang.UnsupportedOperationException\n')
  self.assertEqual(causes.inspect_failure(self.arm,'konclude')['classification'],'ambiguous')
 def test_wrong_runtime_cannot_supply_timeout(self):
  self.state('timeout');p=self.root/'000.json';d=json.loads(p.read_text());d['binary_sha256']='c'*64;p.write_text(json.dumps(d))
  self.assertEqual(causes.inspect_failure(self.arm,'konclude')['classification'],'missing_evidence')
 def test_stale_checkpoint_is_not_finalized(self):
  self.arm['measurement'].pop('rc');self.state('timeout')
  self.assertEqual(causes.inspect_failure(self.arm,'konclude')['classification'],'not_finalized')
 def test_changed_measurement_is_rejected(self):
  (self.root/'measurement.json').write_text('{}')
  self.assertEqual(causes.inspect_failure(self.arm,'konclude')['classification'],'measurement_unavailable_or_changed')
 def test_large_evidence_read_is_bounded_and_offsets_recorded(self):
  p=self.root/'driver.stderr';p.write_bytes(b'x'*(causes.BUDGET*4)+b'\nSTATE_TIMEOUT revision=0\n')
  data,evidence=causes.bounded_read(p)
  self.assertLessEqual(len(data),causes.BUDGET+1);self.assertTrue(evidence['truncated'])
  self.assertEqual(sum(s['length'] for s in evidence['segments']),causes.BUDGET)
  self.assertEqual(causes.inspect_failure(self.arm,'hermit')['classification'],'timeout')

if __name__=='__main__':unittest.main()
