"""Read measured update outputs only after validating their source and raw hashes."""
import json
from pathlib import Path
from measure_classification import digest


def extract(directory, baseline, mode, revision, source_hash, artifact_hash, output):
    directory=Path(directory);record=json.loads((directory/'record.json').read_text())
    if record['artifact_sha256']!=artifact_hash:raise ValueError('measurement artifact mismatch')
    if mode=='cold':
        stage=record
        if stage['source_sha256']!=source_hash:raise ValueError('measurement source mismatch')
        if stage['status']!='executed_unvalidated':return {'status':stage['status']}
        raw=directory/'taxonomy.raw'
        if digest(raw)!=record['files']['taxonomy.raw']['sha256']:raise ValueError('taxonomy changed')
        text=raw.read_text();fmt=record['output_format']
    else:
        stages=record['revisions']
        if revision>=len(stages):return {'status':'missing_revision'}
        stage=stages[revision]
        if stage['revision']!=revision:raise ValueError('revision ordering changed')
        if stage.get('source_sha256',stage['sha256'])!=source_hash:raise ValueError('revision source mismatch')
        if stage['status']!='executed_unvalidated':return {'status':stage['status']}
        if baseline=='km':
            raw=directory/f'{revision:03}.response.json'
            if digest(raw)!=stage['response_sha256']:raise ValueError('session response changed')
            response=json.loads(raw.read_text())
            if response.get('status')!='ok' or response.get('revision')!=revision:raise ValueError('invalid KM response revision')
            text=json.dumps(response['result']);fmt='km-json'
        elif baseline=='konclude':
            raw=directory/f'{revision:03}.taxonomy.json'
            if digest(raw)!=stage['taxonomy_sha256']:raise ValueError('session taxonomy changed')
            text=raw.read_text();fmt='km-json'  # normalized full-IRI relation schema
        else:
            raw=directory/'session'/f'{revision:03}.taxonomy.tsv'
            if digest(raw)!=stage['taxonomy_sha256']:raise ValueError('session taxonomy changed')
            text=raw.read_text();fmt='owlapi-tsv'
    output=Path(output);output.parent.mkdir(parents=True,exist_ok=True);output.write_text(text)
    return {'status':'extracted_requires_semantic_audit','format':fmt,'raw_sha256':digest(raw),
            'extracted_sha256':digest(output),'measurement_receipt_sha256':digest(directory/'record.json'),
            'wall_s':stage.get('wall_s'),'peak_bytes':stage.get('peak_bytes',stage.get('sampled_peak_bytes'))}
