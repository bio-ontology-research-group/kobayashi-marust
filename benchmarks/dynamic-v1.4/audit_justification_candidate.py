#!/usr/bin/env python3
"""Known-family checks for the five frozen candidate explanation controls."""
import argparse,csv,json,re
from collections import Counter
from pathlib import Path
from audit_justification_main import audit,tsv

def main(a):
 rows=[]
 for name in ['unsatisfiable','inconsistent','two-paths','noise','negative']:
  case=a.root/name;task=json.loads((case/'task.json').read_text())
  for limit in [1,10,100]:
   for arm in ['km-native','km-common']:
    p=case/'results'/str(limit)/arm;row=audit(task,p,limit,arm)
    if name=='negative' and row['status']=='invalid_output':
     report=json.loads((p/'report.json').read_text()) if arm=='km-native' else tsv(p/'metrics.tsv')
     negative=report['status']=='not-entailed' if arm=='km-native' else report['entailed']=='false'
     complete=report['enumerationComplete'] if arm=='km-native' else report['enumeration_complete']=='true'
     v=p/'independent-hermit';inv=json.loads((v/'invocation.json').read_text())
     checks=list(csv.DictReader((v/'verification.tsv').open(),delimiter='\t'))
     if negative and complete and row['supports']==0 and inv['exit_code']==0 and not checks and (v/'source-entailed.txt').read_text().strip()=='false':row['status']='correct'
    if row['status']=='correct':
     known=0 if name=='negative' else (min(limit,2) if name in ['two-paths','noise'] else 1)
     if row['supports']!=known:row['status']='wrong_known_family_count'
     families=[]
     for f in p.glob('support-*.ofn'):
      pairs=re.findall(r'SubClassOf\(\s*<http://example.org/([ABCD])>\s+<http://example.org/([ABCD])>\s*\)',f.read_text())
      if name in ['two-paths','noise']:families.append(frozenset(pairs))
     if families:
      allowed={frozenset([('A','B'),('B','D')]),frozenset([('A','C'),('C','D')])}
      if len(families)!=len(set(families)) or any(f not in allowed for f in families):row['status']='wrong_known_family'
    rows.append(row)
 result={'rows':rows,'counts':dict(Counter(r['status'] for r in rows))};a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['counts']))
 if any(r['status']!='correct' for r in rows):raise SystemExit(1)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('output',type=Path);main(p.parse_args())
