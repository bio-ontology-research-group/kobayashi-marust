"""Strict binding checks for complete common-driver correction cohorts."""
import hashlib,json
from pathlib import Path

OLD = "JsonNode response=mapper.readTree(process.getInputStream());"
NEW = """// Jackson closes an InputStream after parsing its first JSON value.
                // Drain to EOF first so the worker can finish writing before
                // we inspect its exit status (including the trailing newline).
                JsonNode response=mapper.readTree(process.getInputStream().readAllBytes());"""

def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def arms(task):
 if 'arms' in task:return task['arms']
 out=['km-native','km-common','hermit-common','jfact-common','openllet-common']
 if task.get('library'):out+=['hermit-library','jfact-library','openllet-library']
 if task.get('konclude'):out+=['konclude-common']
 if task['el']:out+=['elk-common','whelk-common']
 return out

def validate(original, corrected):
 issues=[]
 def bad(s):issues.append(s)
 arm=corrected['spec'].get('correction_arm','km-common')
 if arm not in {'km-common','konclude-common'}:bad('unsupported correction arm')
 oldroot=Path(original['spec']['manifest_root']);newroot=Path(corrected['spec']['manifest_root'])
 oldtasks={p.stem:p for p in (oldroot/'tasks').glob('*.json')}
 newtasks={p.stem:p for p in (newroot/'tasks').glob('*.json')}
 if set(oldtasks)!=set(newtasks):bad('correction must cover every original task ID')
 allowed={'arms','classes','driver_manifest','driver_manifest_sha256','konclude',
          'prior_task_sha256','prior_driver_manifest_sha256','harness_revision'}
 for tid in set(oldtasks)&set(newtasks):
  old=json.loads(oldtasks[tid].read_text());new=json.loads(newtasks[tid].read_text())
  if new.get('prior_task_sha256')!=digest(oldtasks[tid]):bad(tid+': prior task hash mismatch')
  if new.get('prior_driver_manifest_sha256')!=old.get('driver_manifest_sha256'):bad(tid+': prior manifest mismatch')
  if arm not in arms(old):bad(tid+': correction arm absent from original task')
  if new.get('arms')!=[arm] or new.get('harness_revision')!='stream-v4':bad(tid+': incorrect correction arm/revision')
  if {k:v for k,v in old.items() if k not in allowed}!={k:v for k,v in new.items() if k not in allowed}:bad(tid+': frozen task changed')
  for field in ['km']:
   if original['manifest'].get(old[field])!=corrected['manifest'].get(new[field]) or old[field] not in original['manifest']:bad(tid+': binary binding changed')
 oldfiles={Path(k).name:(k,v) for k,v in original['manifest'].items() if not k.endswith('.class')}
 newfiles={Path(k).name:(k,v) for k,v in corrected['manifest'].items() if not k.endswith('.class')}
 if len(oldfiles)!=sum(not k.endswith('.class') for k in original['manifest']):bad('ambiguous original artifact basename')
 if len(newfiles)!=sum(not k.endswith('.class') for k in corrected['manifest']):bad('ambiguous corrected artifact basename')
 for name,(path,h) in oldfiles.items():
  if name=='JustificationBenchmark.java':continue
  if name not in newfiles or newfiles[name][1]!=h:bad('unchanged artifact mismatch: '+name)
 try:
  op,oh=oldfiles['JustificationBenchmark.java'];np,nh=newfiles['JustificationBenchmark.java']
  old=Path(op).read_text();new=Path(np).read_text()
  if digest(op)!=oh or digest(np)!=nh:bad('adapter source hash mismatch')
  if old.count(OLD)!=1 or old.replace(OLD,NEW)!=new:bad('adapter differs beyond exact stdout-draining fix')
 except (KeyError,OSError):bad('adapter source binding missing')
 return issues

def select(sources, corrections):
 """No fallback to old measurements, even if corrected attempts failed."""
 replaced={(s['spec']['replaces'],s['spec'].get('correction_arm','km-common')) for s in corrections}
 for source in sources:
  for row in source['rows']:
   row['harness_revision']='stream-v4' if source in corrections else 'original-v3'
   row['comparison_selected']=not((row['source'],row['arm']) in replaced)
