#!/usr/bin/env python3
"""Audit measured extraction artifacts. Completion files alone never imply correctness."""
import argparse,csv,json
from pathlib import Path

def audit(out):
 rows=[]
 for invocation in sorted(out.glob('*/*/invocation.json')):
  p=invocation.parent;limit=int(p.parent.name);arm=p.name
  row=dict(limit=limit,arm=arm,**json.loads(invocation.read_text()))
  rc=row['exit_code']
  if rc:
   row['status']='timeout' if rc==124 else 'error';rows.append(row);continue
  if arm=='km-native':
   report=json.loads((p/'report.json').read_text());n=len(report['justifications']);positive=report['status']=='entailed'
   row.update(supports=n,enumeration_complete=report['enumerationComplete'],oracle_checks=report['classificationChecks'])
  else:
   metrics=dict(line.split('\t',1) for line in (p/'metrics.tsv').read_text().splitlines());n=int(metrics['supports']);positive=metrics['entailed']=='true';row.update(metrics)
  verifiers=list(p.glob('independent-*/verification.tsv'))
  valid=len(verifiers)==1 and n==len(list(p.glob('support-*.ofn'))) and 0<=n<=limit and (n>0 or not positive)
  if len(verifiers)==1:
   v=verifiers[0];checks=list(csv.DictReader(v.open(),delimiter='\t'))
   valid=valid and len(checks)==n and all(r['source_subset']=='true' and r['minimal_entailed']=='true' for r in checks)
   oracle=v.parent/'source-entailed.txt';valid=valid and oracle.exists() and (oracle.read_text().strip()=='true')==positive
  row['status']='correct' if valid else 'unverified_or_incorrect';rows.append(row)
 return rows
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('out',type=Path);a=p.parse_args()
 rows=audit(a.root);a.out.write_text(json.dumps(rows,indent=2)+'\n')
 from collections import Counter
 print(dict(Counter(r['status'] for r in rows)))
