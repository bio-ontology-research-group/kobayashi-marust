#!/usr/bin/env python3
"""Summarize partial/full harness panels without treating completion as correctness."""
import argparse,collections,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('panels',nargs='+',type=Path);ap.add_argument('--output',type=Path);args=ap.parse_args()
summary={'panels':{},'paired':{}};panels=[]
for panel in args.panels:
 rows={};headers=[]
 for path in sorted(panel.glob('*/results.jsonl')):
  for line in path.read_text().splitlines():
   try:row=json.loads(line)
   except json.JSONDecodeError:continue
   if row.get('kind')!='case':headers.append(row);continue
   if row['ont'] in rows:raise ValueError('duplicate ontology '+row['ont'])
   rows[row['ont']]=row
 panels.append(rows)
 summary['panels'][panel.name]={'observed':len(rows),'complete_chunks':sum(1 for _ in panel.glob('*/COMPLETE')),'outcomes':dict(collections.Counter(r['outcome'] for r in rows.values())),'not_ok':[{k:r.get(k) for k in ['ont','outcome','wall_s','peak_rss_kb','skip_reason']} for r in rows.values() if r['outcome']!='ok']}
if panels:
 baseline=panels[0]
 for path,other in zip(args.panels[1:],panels[1:]):
  common=baseline.keys()&other.keys()
  counts=collections.Counter((baseline[k]['outcome'],other[k]['outcome']) for k in common)
  summary['paired'][path.name]={'common':len(common),'outcomes':[{'baseline':a,'other':b,'count':n} for (a,b),n in sorted(counts.items())],'new_completions':[k for k in sorted(common) if baseline[k]['outcome']!='ok' and other[k]['outcome']=='ok'],'lost_completions':[k for k in sorted(common) if baseline[k]['outcome']=='ok' and other[k]['outcome']!='ok'],'changed_output_hashes':[k for k in sorted(common) if baseline[k]['outcome']==other[k]['outcome']=='ok' and baseline[k].get('out_sha256')!=other[k].get('out_sha256')]}
text=json.dumps(summary,indent=2)+'\n'
if args.output:args.output.write_text(text)
else:print(text,end='')
