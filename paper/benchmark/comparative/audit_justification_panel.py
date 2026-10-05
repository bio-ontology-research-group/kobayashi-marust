"""Check every frozen justification case, retaining failures and missing outputs."""
import csv,json,sys
from pathlib import Path
from collections import Counter
from audit_justification import audit
from measure_classification import digest
from run_set import load as load_run_set

root,task,job=Path(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
runs=load_run_set(root,sys.argv[4] if len(sys.argv)>4 else None)
source=json.loads((root/'workload-selection.json').read_text())['selected'][task]
inventory={r['id']:r for r in json.loads((root/runs['inventory']).read_text())['artifacts']}
out=root/('justification-audit-'+job)/source['ontology'];out.mkdir(parents=True,exist_ok=False)
result={'ontology':source['ontology'],'source_sha256':source['sha256'],'status':'running','run_set':runs,'cases':[],'runner_sha256':digest(__file__)}
def publish():
 p=out/'audit.json.part';p.write_text(json.dumps(result,indent=2)+'\n');p.replace(out/'audit.json')
publish()
try:
 assert digest(source['path'])==source['sha256'],'source changed'
 prepared=root/('prepared-queries-'+runs['queries_preparation'])/source['ontology']
 receipt=json.loads((prepared/'receipt.json').read_text());result['preparation_receipt_sha256']=digest(prepared/'receipt.json')
 assert receipt['source_sha256']==source['sha256'],'preparation source mismatch'
 if receipt['status']!='prepared':
  result.update(status='query_preparation_failed',error=receipt.get('error'))
 else:
  query_file=prepared/'queries/queries.tsv'
  assert digest(query_file)==receipt['files']['queries.tsv']['sha256'],'query manifest changed'
  with query_file.open() as stream:queries=list(csv.DictReader(stream,delimiter='\t'))
  result['eligible_queries']=len(queries)
  for query in queries:
   module=prepared/'queries'/(query['query']+'.ofn')
   assert query['module_sha256']==receipt['files'][module.name]['sha256']==digest(module),'module binding failed'
   for baseline,generator in inventory.items():
    jobid=runs['justifications_km' if baseline=='km' else 'justifications_native' if baseline=='rustdl' else 'justifications_external' if baseline in ['konclude','sequoia','more'] else 'justifications_whelk' if baseline=='whelk' else 'justifications_java']
    verifier=inventory['jfact' if baseline=='hermit' else 'hermit']
    for repetition in range(3):
     directory=root/('java-justifications-'+jobid)/source['ontology']/baseline/f'repetition-{repetition}'/query['query']
     case={'baseline':baseline,'query':query['query'],'repetition':repetition}
     if not (directory/'record.json').exists():
      case['status']='missing_measurement'
      parent=directory.parents[1]/'summary.json'
      if parent.exists():
       parent_record=json.loads(parent.read_text());case.update(parent_status=parent_record['status'],parent_error=parent_record.get('error'))
       for item in parent_record.get('cases',[]):
        if item.get('query')==query['query'] and item.get('repetition')==repetition:
         case.update(status=item['status'],error=item.get('error'))
     else:
      try:case.update(audit(directory,generator,verifier,source['sha256'],query['module_sha256'],[query['sub_iri'],query['super_iri']]))
      except Exception as error:case.update(status='evidence_validation_error',error=str(error))
     result['cases'].append(case)
   publish()
  result['status']='audited' if queries else 'no_eligible_inferred_queries'
except Exception as error:result.update(status='audit_error',error=str(error))
result['counts']=dict(Counter(c['status'] for c in result['cases']));publish()
