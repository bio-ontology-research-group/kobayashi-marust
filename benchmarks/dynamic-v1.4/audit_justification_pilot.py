#!/usr/bin/env python3
"""Analytic support-family and independent minimality audit; failures stay visible."""
import argparse,csv,json,re
from pathlib import Path

def audit(root):
 rows=[]
 for case in ['two-paths','noise','negative']:
  for limit in [1,10]:
   for arm in ['km-native','hermit-common','jfact-common','openllet-common','elk-common','whelk-common','km-common','konclude-common']:
    p=root/case/str(limit)/arm
    row=dict(case=case,limit=limit,arm=arm,status='incomplete')
    if not (p/'exit-code').exists(): rows.append(row);continue
    rc=int((p/'exit-code').read_text());row['exit_code']=rc
    if rc: row['status']='timeout' if rc==124 else 'error';rows.append(row);continue
    if arm=='km-native':
     v=json.loads((p/'report.json').read_text());n=len(v['justifications']);complete=v['enumerationComplete']
     positive=v['status']=='entailed';row['checks']=v['classificationChecks']
    else:
     v=dict(x.split('\t',1) for x in (p/'metrics.tsv').read_text().splitlines())
     n=int(v['supports']);complete=v['enumeration_complete']=='true';positive=v['entailed']=='true';row['checks']=int(v['oracle_checks'])
    expected=0 if case=='negative' else min(limit,2)
    valid=n==expected and positive==(case!='negative') and complete==(case=='negative' or limit>=2)
    verifications=list(p.glob('independent-*/verification.tsv'))
    if len(verifications)!=1:valid=False
    else:
     checks=list(csv.DictReader(verifications[0].open(),delimiter='\t'))
     valid=valid and len(checks)==n and all(r['source_subset']=='true' and r['minimal_entailed']=='true' for r in checks)
    supports=list(p.glob('support-*.ofn'))
    families=[]
    for support in supports:
     text=support.read_text();pairs=re.findall(r'SubClassOf\(\s*(?:<urn:km:just:|:)([ABCD])>?\s+(?:<urn:km:just:|:)([ABCD])>?\s*\)',text)
     families.append(frozenset(pairs))
    known={frozenset([('A','B'),('B','D')]),frozenset([('A','C'),('C','D')])}
    valid=valid and len(families)==n and len(set(families))==n and all(f in known for f in families)
    row.update(status='correct' if valid else 'incorrect',supports=n,enumeration_complete=complete)
    rows.append(row)
 return rows

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
 rows=audit(a.root);a.output.write_text(json.dumps(rows,indent=2)+'\n')
 from collections import Counter
 print(dict(Counter(r['status'] for r in rows)))
