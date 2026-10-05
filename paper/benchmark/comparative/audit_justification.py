"""Audit measured explanation evidence; generation alone is never a success."""
import json
from pathlib import Path
from measure_classification import digest


def audit(directory, generator, verifier, source_hash, module_hash, query):
    directory=Path(directory)
    record=json.loads((directory/'record.json').read_text())
    expected={'generator':generator['id'],'verifier':verifier['id'],
              'source_sha256':source_hash,'module_sha256':module_hash,'query':query}
    for key,value in expected.items():
        if record.get(key)!=value:raise ValueError('measurement binding mismatch: '+key)
    if generator['id']==verifier['id']:raise ValueError('verifier is not independent')
    result={'status':record['status'],'measurement_receipt_sha256':digest(directory/'record.json')}
    if record['status']!='independently_verified':return result
    for row in [generator,verifier]:
        if record['artifacts'].get(row['id'])!=row['sha256']:raise ValueError('runtime hash mismatch')
    stages=record['stages']
    if len(stages)!=2 or [s['name'] for s in stages]!=['generation','verification']:
        raise ValueError('missing generation or verification stage')
    for stage in stages:
        if stage['status']!='executed' or stage['exit_code']!=0:raise ValueError('unsuccessful verification pipeline')
        if stage['timeout_s']!=240 or stage['memory_mib']!=20480 or len(stage['cpu_affinity'])!=1:
            raise ValueError('resource protocol differs')
        if stage['peak_bytes']>20480*1024**2:raise ValueError('memory limit exceeded')
    for filename,key in [('explanation.tsv.ofn','justification_sha256'),('verification.tsv','verification_sha256')]:
        actual=digest(directory/filename)
        if actual!=record[key] or actual!=record['files'][filename]['sha256']:
            raise ValueError('evidence changed: '+filename)
    lines=(directory/'verification.tsv').read_text().splitlines()
    if not lines or lines[-1]!='Z\tcomplete':raise ValueError('incomplete verification receipt')
    fields={}
    for line in lines[:-1]:
        parts=line.split('\t')
        if len(parts)!=3 or parts[0]!='M' or parts[1] in fields:raise ValueError('invalid verification receipt')
        fields[parts[1]]=parts[2]
    for key in ['source_subset','entailed','subset_minimal']:
        if fields.get(key)!='true':raise ValueError('verification failed: '+key)
    count=int(fields['logical_axioms']);checks=int(fields['checks'])
    if count<0 or checks!=count+1:raise ValueError('minimality verification did not check every deletion')
    if 'justification_axioms' in record and record['justification_axioms']!=count:
        raise ValueError('generator and verifier support sizes differ')
    return dict(result,status='verified_evidence_intact',logical_axioms=count,
                generation_wall_s=stages[0]['wall_s'],generation_peak_bytes=stages[0]['peak_bytes'],
                verification_wall_s=stages[1]['wall_s'],verification_peak_bytes=stages[1]['peak_bytes'])
