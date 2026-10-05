"""Measure three retained sessions using the fresh panel's verified revisions."""
import json,sys
from pathlib import Path
from measure_classification import digest
from measure_retained_konclude import measure
from owllink_requests import axioms
from taxonomy import OWL
root,task,job,preparation_job,conversion_job=Path(sys.argv[1]),int(sys.argv[2]),sys.argv[3],sys.argv[4],sys.argv[5]
source=json.loads((root/'workload-selection.json').read_text())['selected'][task]
out=root/('konclude-retained-'+job)/source['ontology'];out.mkdir(parents=True,exist_ok=False)
summary={'ontology':source['ontology'],'source_sha256':source['sha256'],'status':'preparing','repetitions':[], 'runner_sha256':digest(__file__)}
def publish():
 p=out/'summary.json.part';p.write_text(json.dumps(summary,indent=2)+'\n');p.replace(out/'summary.json')
publish()
try:
 prepared=root/('prepared-updates-'+preparation_job)/source['ontology']
 receipt=json.loads((prepared/'receipt.json').read_text())
 assert receipt['status']=='prepared' and receipt['source_sha256']==source['sha256'],'unverified prepared input'
 verification=prepared/'revisions/verification.tsv'
 assert digest(verification)==receipt['files']['verification.tsv'] and verification.read_text().endswith('status\tpassed\n'),'preservation gate failed'
 revisions=[]
 for i in range(5):
  converted=root/('konclude-updates-'+conversion_job)/source['ontology']/'conversion'/f'{i:03}'
  record=json.loads((converted/'record.json').read_text())
  assert record['status']=='converted','conversion failed'
  xml=converted/'input.owlxml';proof=converted/'roundtrip.tsv'
  assert digest(xml)==record['runtime_source_sha256'],'converted input changed'
  assert digest(proof)==record['receipt_sha256'],'conversion proof changed'
  lines=proof.read_text().splitlines();assert lines[-1]=='Z\tcomplete','incomplete conversion proof'
  fields=dict(line.split('\t',2)[1:] for line in lines if line.startswith('M\t'))
  expected={'source_sha256':receipt['files'][f'{i:03}.ofn'],'output_sha256':digest(xml),'serialization':'owlxml','roundtrip_logical_axioms_equal':'true','roundtrip_signature_equal':'true'}
  assert all(fields.get(k)==v for k,v in expected.items()),'conversion/source binding failed'
  classes=sorted({e.attrib['IRI'] for ax in axioms(xml).values() for e in ax.iter() if e.tag=='{'+OWL+'}Class'})
  revisions.append({'path':str(xml),'sha256':digest(xml),'source_sha256':expected['source_sha256'],'conversion_receipt_sha256':digest(proof),'classes':classes})
 row=next(r for r in json.loads((root/'artifact-inventory-53198415.json').read_text())['artifacts'] if r['id']=='konclude')
 summary.update(status='running',preparation_receipt_sha256=digest(prepared/'receipt.json'));publish()
 for repetition in range(3):
  result=measure(row,revisions,out/f'repetition-{repetition}')
  summary['repetitions'].append({'repetition':repetition,'status':result['status'],'error':result.get('error')});publish()
 summary['status']='measurement_complete_requires_semantic_audit'
except Exception as error:summary.update(status='preparation_or_adapter_error',error=str(error))
publish();print(json.dumps(summary))
