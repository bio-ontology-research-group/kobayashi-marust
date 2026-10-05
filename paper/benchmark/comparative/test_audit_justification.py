import json,shutil,tempfile,unittest
from pathlib import Path
from audit_justification import audit

class JustificationAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        source=Path(__file__).resolve().parents[3]/'results/benchmarks/2026-10-04-v1.4.5-comparative/external-justification-pilot-53203563/konclude'
        self.path=Path(self.temp.name)/'case';shutil.copytree(source,self.path)
        self.record=json.loads((self.path/'record.json').read_text())
    def check(self):
        r=self.record
        return audit(self.path,{'id':r['generator'],'sha256':r['artifacts'][r['generator']]},
                     {'id':r['verifier'],'sha256':r['artifacts'][r['verifier']]},r['source_sha256'],r['module_sha256'],r['query'])
    def test_real_independently_verified_support(self):
        self.assertEqual(self.check()['logical_axioms'],2)
    def test_tampered_support_rejected(self):
        (self.path/'explanation.tsv.ofn').write_text('Ontology()')
        with self.assertRaises(ValueError):self.check()
    def test_generation_without_verification_is_not_success(self):
        self.record['status']='verification_timeout'
        (self.path/'record.json').write_text(json.dumps(self.record))
        self.assertEqual(self.check()['status'],'verification_timeout')

if __name__=='__main__':unittest.main()
