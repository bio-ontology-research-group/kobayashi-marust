"""Select a deterministic size-stratified source panel, without timing results."""
import argparse,collections,hashlib,json,pathlib
p=argparse.ArgumentParser();p.add_argument('inventory',type=pathlib.Path);p.add_argument('output',type=pathlib.Path);a=p.parse_args()
rows=json.loads(a.inventory.read_text())['results'];assert len(rows)==1920
bins=collections.defaultdict(list);excluded=[]
for row in rows:
 if row['status']!='checks_passed':excluded.append({'ontology':row['ontology'],'sha256':row['sha256'],'reason':row['status'],'diagnostic':row['message']});continue
 size=pathlib.Path(row['path']).stat().st_size
 band=next((i for i,limit in enumerate([100*1024,1024*1024,10*1024*1024]) if size<limit),3)
 rank=hashlib.sha256(('km-v145-panel-v1\0'+row['sha256']).encode()).hexdigest()
 bins[band].append({'ontology':row['ontology'],'sha256':row['sha256'],'path':row['path'],'bytes':size,'size_band':band,'selection_rank':rank})
selected=[row for band in sorted(bins) for row in sorted(bins[band],key=lambda r:(r['selection_rank'],r['ontology']))[:20]]
report={'selection':'20 lowest domain-separated source-hash ranks in each size band; all if fewer than 20','size_boundaries_bytes':[102400,1048576,10485760],'eligible_counts':{str(k):len(v) for k,v in bins.items()},'selected':selected,'excluded_invalid':excluded,'classification_scope':'All 1920 original inputs, including invalid inputs, remain in classification'}
a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'selected':len(selected),'eligible_counts':report['eligible_counts'],'excluded_invalid':len(excluded)}))
