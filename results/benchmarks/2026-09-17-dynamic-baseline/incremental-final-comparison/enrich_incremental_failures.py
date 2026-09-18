#!/usr/bin/env python3
"""Bounded, read-only failure evidence sidecar for immutable incremental audits.

A parser rejection is labelled parse_error, not assumed unsupported. Missing or
contradictory evidence never changes the supervisor's status. No raw files are
modified. Run after the audited jobs terminate; stale records are unclassified.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import xml.etree.ElementTree as ET

BUDGET=131072

def digest(data):return hashlib.sha256(data).hexdigest()

def bounded_read(path):
    """Hash exact retained segments; do not claim a full-file hash if truncated."""
    if not path.is_file():return None,None
    size=path.stat().st_size
    with path.open('rb') as f:
        if size<=BUDGET:segments=[(0,f.read(BUDGET))]
        else:
            segments=[(0,f.read(BUDGET//2))]
            f.seek(size-BUDGET//2);segments.append((size-BUDGET//2,f.read(BUDGET//2)))
    data=b'\n'.join(segment for _,segment in segments)
    return data,dict(path=str(path),size=size,truncated=size>BUDGET,
        segments=[dict(offset=offset,length=len(data),sha256=digest(data)) for offset,data in segments])

def inspect_failure(arm,reasoner):
    m=arm.get('measurement',{});status=arm.get('status','missing')
    result=dict(reported_status=status,classification='missing_evidence',findings=[])
    if status=='ok':result['classification']='not_a_failure';return result
    if 'rc' not in m or m['rc'] is None or status in ('running','missing','unknown','invalid_measurement'):
        result['classification']='not_finalized';return result
    directory=Path(arm['path'])
    measurement,measurement_source=bounded_read(directory/'measurement.json')
    if measurement is None or measurement_source['truncated'] or digest(measurement)!=arm.get('measurement_sha256'):
        result['classification']='measurement_unavailable_or_changed';return result
    def finding(kind,source,text):
        result['findings'].append(dict(kind=kind,evidence=source,excerpt=text[:600]))
    # Worker deadlines are explicitly printed by both Java and KM adapters.
    data,source=bounded_read(directory/'driver.stderr')
    if data is not None:
        text=data.decode(errors='replace')
        for pattern,kind in [(r'STATE_TIMEOUT(?: revision=\d+| after \d+ seconds)','timeout'),
             (r'(?:java\.lang\.)?UnsupportedOperationException(?:[^\n]{0,180})','unsupported'),
             (r'UnsupportedEntailmentTypeException(?:[^\n]{0,180})','unsupported')]:
            match=re.search(pattern,text)
            if match:finding(kind,source,match.group(0))
    if reasoner=='konclude':
        revision=m.get('completed_states')
        if isinstance(revision,int) and 0<=revision<m.get('expected_states',0):
            data,source=bounded_read(directory/f'{revision:03d}.json')
            if data is not None and not source['truncated']:
                try:row=json.loads(data)
                except (ValueError,UnicodeError):row={}
                bound=(row.get('revision')==revision and row.get('reasoner')=='konclude' and row.get('arm')=='fresh'
                       and row.get('binary_sha256')==m.get('runtime_sha256'))
                if bound and row.get('status')=='timeout':finding('timeout',source,'Konclude adapter state status=timeout; revision='+str(revision))
                elif bound and row.get('status')=='output_error':
                    xml,evidence=bounded_read(directory/f'{revision:03d}.response.xml')
                    if xml is not None and not evidence['truncated']:
                        try:
                            root=ET.fromstring(xml)
                            errors=[e for e in root.iter() if e.tag.rsplit('}',1)[-1] in ('Error','ErrorText','UnsupportedCommandError')]
                            text='\n'.join(e.get('error','')+' '+(e.text or '') for e in errors)
                            parse=re.search(r'(?:All parsers failed[^\n]*|OWL2/Functional ontology parsing error:[^\n]*)',text)
                            if parse:finding('parse_error',evidence,parse.group(0))
                            unsupported=next((e for e in errors if e.tag.rsplit('}',1)[-1]=='UnsupportedCommandError'),None)
                            if unsupported is not None:finding('unsupported',evidence,ET.tostring(unsupported,encoding='unicode'))
                            explicit=re.search(r'\b(?:UnsupportedOperationException|UnsupportedEntailmentTypeException)\b[^\n]*',text)
                            if explicit:finding('unsupported',evidence,explicit.group(0))
                        except ET.ParseError:pass
    kinds={f['kind'] for f in result['findings']}
    if len(kinds)==1:result['classification']=next(iter(kinds))
    elif len(kinds)>1:result['classification']='ambiguous'
    return result

def enrich(specs,out):
    entries=[];sources=[]
    for spec in specs:
        label,name=spec.split('=',1);path=Path(name);raw=path.read_bytes();audit=json.loads(raw);audit_sha=digest(raw)
        sources.append(dict(label=label,path=str(path),sha256=audit_sha))
        for case,c in audit['cases'].items():
            for repetition,r in c.get('repetitions',{}).items():
                for key,arm in r['arms'].items():
                    if arm.get('status')=='ok':continue
                    reasoner,mode=key.split('/',1)
                    entry=dict(label=label,audit_sha256=audit_sha,case=case,repetition=repetition,reasoner=reasoner,arm=mode,
                        measurement_sha256=arm.get('measurement_sha256',''),**inspect_failure(arm,reasoner))
                    entries.append(entry)
    report=dict(schema=1,enricher_sha256=digest(Path(__file__).read_bytes()),max_bytes_per_evidence_file=BUDGET,
        scope='direct failure evidence only; no speculative unsupported classification; raw statuses preserved',audits=sources,entries=entries)
    with out.open('x') as stream:json.dump(report,stream,indent=2);stream.write('\n')
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--audit',action='append',required=True);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();enrich(a.audit,a.out)
