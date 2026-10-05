import hashlib,json,tempfile,unittest
from pathlib import Path
from update_outputs import extract

class UpdateOutputTests(unittest.TestCase):
    def test_retained_revision_and_hash_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);response={'status':'ok','revision':0,'result':{'consistent':True,'subsumptions':[],'unsatisfiable':[]}}
            raw=root/'000.response.json';raw.write_text(json.dumps(response))
            stage={'revision':0,'sha256':'source','status':'executed_unvalidated','response_sha256':hashlib.sha256(raw.read_bytes()).hexdigest()}
            (root/'record.json').write_text(json.dumps({'artifact_sha256':'binary','revisions':[stage]}))
            result=extract(root,'km','retained',0,'source','binary',root/'extracted')
            self.assertEqual(result['status'],'extracted_requires_semantic_audit')
            with self.assertRaises(ValueError):extract(root,'km','retained',0,'other','binary',root/'wrong')
            raw.write_text('{}')
            with self.assertRaises(ValueError):extract(root,'km','retained',0,'source','binary',root/'wrong')

    def test_timeout_does_not_become_a_taxonomy(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'record.json').write_text(json.dumps({'artifact_sha256':'binary','source_sha256':'source','status':'timeout'}))
            self.assertEqual(extract(root,'km','cold',0,'source','binary',root/'out')['status'],'timeout')
            self.assertFalse((root/'out').exists())

if __name__=='__main__':unittest.main()
