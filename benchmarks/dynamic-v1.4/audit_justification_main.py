#!/usr/bin/env python3
"""Audit every scheduled extraction and independent minimality witness."""
import argparse,csv,hashlib,json,statistics
from collections import Counter,defaultdict
from pathlib import Path

def tsv(path):
 return dict(line.split('\t',1) for line in path.read_text().splitlines())

def audit(task,dest,limit,arm):
 row={k:task[k] for k in ['ontology','query_id','track','repetition','warmup']}
 row.update(limit=limit,arm=arm,status='missing')
 inv=dest/'invocation.json'
 if not inv.exists():return row
 v=json.loads(inv.read_text());row.update(elapsed_s=v['elapsed_s'],peak_rss_bytes=v.get('sampled_peak_process_tree_rss_bytes'))
 if v.get('status')=='memout':row['status']='memout';return row
 if v['exit_code']!=0:row['status']='timeout' if v['exit_code']==124 else 'error';return row
 try:
  supports=sorted(dest.glob('support-*.ofn'))
  if arm=='km-native':
   report=json.loads((dest/'report.json').read_text())
   count=len(report['justifications']);complete=report['enumerationComplete']
   positive=report['status']=='entailed'
  else:
   report=tsv(dest/'metrics.tsv');count=int(report['supports']);complete=report['enumeration_complete'];positive=report['entailed']=='true'
   row['first_s']=float(report['first_s']);row['extraction_s']=float(report['total_s'])
  row.update(supports=count,enumeration_complete=complete)
  if not positive or count==0 or count!=len(supports) or count>limit:row['status']='invalid_output';return row
  validator='jfact' if arm.startswith('hermit-') else 'hermit'
  verify=dest/('independent-'+validator)
  check=json.loads((verify/'invocation.json').read_text())
  if check['exit_code']!=0:row['status']='verification_timeout' if check['exit_code']==124 else 'verification_error';return row
  with (verify/'verification.tsv').open() as stream:rows=list(csv.DictReader(stream,delimiter='\t'))
  if (verify/'source-entailed.txt').read_text().strip()!='true':row['status']='source_disagreement';return row
  if set(r['support'] for r in rows)!=set(p.name for p in supports) or len(rows)!=len(supports):row['status']='verification_count_mismatch';return row
  if any(r['source_subset']!='true' or r['minimal_entailed']!='true' for r in rows):row['status']='invalid_support';return row
  row['status']='correct'
 except (OSError,ValueError,KeyError,TypeError) as e:row['status']='incomplete_evidence';row['detail']=str(e)
 return row

def main(args):
 root=args.root;rows=[];integrity=[]
 normalized=defaultdict(list)
 if args.normalized and args.normalized.exists():
  with args.normalized.open() as stream:
   for row in csv.DictReader(stream,delimiter='\t'):normalized[str(Path(row['support']).parent)].append(row['sha256'])
 for file in sorted((root/'tasks').glob('*.json')):
  task=json.loads(file.read_text());result=root/'results'/file.stem
  manifest=result/'driver-manifest.json'
  if manifest.exists() and hashlib.sha256(manifest.read_bytes()).hexdigest()!=task['driver_manifest_sha256']:integrity.append(file.stem+': changed driver receipt')
  arms=['km-native','km-common','hermit-common','jfact-common','openllet-common']
  if task.get('library'):arms+=['hermit-library','jfact-library','openllet-library']
  if task.get('konclude'):arms+=['konclude-common']
  if task['el']:arms+=['elk-common','whelk-common']
  for limit in task['limits']:
   for arm in task.get('arms',arms):
    row=audit(task,result/str(limit)/arm,limit,arm)
    support_hashes=normalized.get(str(Path(file.stem)/str(limit)/arm))
    if support_hashes is not None:
     row['distinct_logical_supports']=len(set(support_hashes))
     row['duplicate_logical_supports']=len(support_hashes)-len(set(support_hashes))
     if row.get('supports')!=len(support_hashes):row['status']='normalization_count_mismatch'
    elif args.normalized and row['status']=='correct':row['status']='normalization_missing'
    rows.append(row)
 groups=defaultdict(list)
 for row in rows:
  if not row['warmup']:groups[(row['track'],row['limit'],row['arm'])].append(row)
 summaries=[]
 for (track,limit,arm),group in sorted(groups.items()):
  good=[r for r in group if r['status']=='correct']
  summaries.append(dict(track=track,limit=limit,arm=arm,scheduled=len(group),statuses=dict(Counter(r['status'] for r in group)),median_correct_wall_s=statistics.median(r['elapsed_s'] for r in good) if good else None))
 report={'rows':rows,'integrity_errors':integrity,'status_counts':dict(Counter(r['status'] for r in rows)),'measured_summaries':summaries,'notes':['Conditional medians describe only correct completed attempts; use paired per-query/repetition rows for speed comparisons.','Warmup is excluded from measured summaries. Bounded enumeration does not prove all supports found.','Process-tree peak RSS is sampled at 50ms and can miss shorter peaks.']}
 args.output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'attempts':len(rows),'status_counts':report['status_counts'],'integrity_errors':integrity}))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('output',type=Path);p.add_argument('--normalized',type=Path);main(p.parse_args())
