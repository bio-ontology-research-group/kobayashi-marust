#!/usr/bin/env python3
"""Render frozen justification matrices, including missing attempts and evidence.

Config: {"sources":[{"label":"baseline-original","manifest_root":"...",
"results_root":"...","audit":"...","normalized":"..."}],
"km_final_sources":[{same fields}], "validation_only":false}.
manifest_root contains tasks/, driver-manifest.json and panel-status.json.
Final KM sources must reproduce every baseline case/repetition with two KM arms.
No input artifacts are changed. Missing audit/results are reported, not omitted.
"""
import argparse,csv,hashlib,json,math,statistics
from collections import Counter,defaultdict
from pathlib import Path
from audit_justification_main import audit
import justification_corrections


def sha(path):
 return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read_json(path,default=None,tolerant=False):
 try:return json.loads(Path(path).read_text()) if path and Path(path).exists() else default
 except (OSError,ValueError):
  if tolerant:return default
  raise

arms = justification_corrections.arms

def case_key(task):
 return tuple(task[k] for k in ['ontology','query_hash','track','sha256','sub','super','repetition'])

def audit_key(row):
 return tuple(row[k] for k in ['ontology','query_id','track','repetition','limit','arm'])

def file_hashes(manifest,suffix):
 return sorted(v for k,v in manifest.items() if k.endswith(suffix))

def spread(values):
 if not values:return dict(n=0,median=None,minimum=None,maximum=None,iqr=None,mad=None)
 values=sorted(values);med=statistics.median(values)
 def quantile(p):
  x=(len(values)-1)*p;i=int(x);return values[i]+(values[min(i+1,len(values)-1)]-values[i])*(x-i)
 return dict(n=len(values),median=med,minimum=values[0],maximum=values[-1],iqr=quantile(.75)-quantile(.25),mad=statistics.median(abs(v-med) for v in values))

def table(path,rows):
 keys=list(dict.fromkeys(k for r in rows for k in r))
 with path.open('w',newline='') as stream:
  writer=csv.DictWriter(stream,keys,delimiter='\t');writer.writeheader()
  for row in rows:writer.writerow({k:json.dumps(v,sort_keys=True) if isinstance(v,(dict,list,tuple)) else v for k,v in row.items()})

def evidence_source(spec,final=False):
 root=Path(spec['manifest_root']);resultroot=Path(spec['results_root']);artifacts=[];issues=[]
 def artifact(path,kind):
  p=Path(path)
  artifacts.append(dict(source=spec['label'],kind=kind,path=str(p),present=p.exists(),sha256=sha(p) if p.is_file() else None))
 for key,name in [('audit','independent_audit'),('normalized','logical_normalization')]:
  if spec.get(key):artifact(spec[key],name)
 driver=root/'driver-manifest.json';artifact(driver,'driver_manifest');manifest=read_json(driver,{})
 receipt_hash=sha(driver) if driver.exists() else None
 tasks=[]
 for p in sorted((root/'tasks').glob('*.json')):
  artifact(p,'frozen_task');task=read_json(p)
  if task['warmup']!=(task['repetition']==0) or task['repetition'] not in range(6):issues.append('invalid repetition/warmup '+str(p))
  if task['limits']!=[1,10,100]:issues.append('unexpected limits '+str(p))
  if task['driver_manifest_sha256']!=receipt_hash:issues.append('driver receipt mismatch '+str(p))
  if final and set(arms(task))!={'km-native','km-common'}:issues.append('final source must contain exactly two KM arms '+str(p))
  tasks.append((p.stem,task))
 if not tasks:issues.append('no frozen tasks: '+str(root))
 countfile=root/'task-count.txt'
 if not countfile.exists() or int(countfile.read_text())!=len(tasks):issues.append('frozen task-count mismatch: '+str(root))
 check=read_json(spec.get('audit'),{},tolerant=True);audit_rows={}
 for row in check.get('rows',[]):
  key=audit_key(row)
  if key in audit_rows:issues.append('duplicate audit row '+str(key))
  audit_rows[key]=row
 issues.extend(check.get('integrity_errors',[]))
 normalized=defaultdict(dict)
 if spec.get('normalized') and Path(spec['normalized']).exists():
  with Path(spec['normalized']).open() as stream:
   for row in csv.DictReader(stream,delimiter='\t'):
    path=Path(row['support']);key=str(path.parent)
    if path.name in normalized[key]:issues.append('duplicate normalization path '+str(path))
    normalized[key][path.name]=row['sha256']
 rows=[];expected_audit=set();case_inventory={}
 for taskid,task in tasks:
  case=case_key(task)
  if case in case_inventory:issues.append('duplicate frozen case '+str(case))
  case_inventory[case]=task
  dest=resultroot/taskid;task_issues=[]
  taskcopy=read_json(dest/'task.json',tolerant=True)
  if taskcopy!=task:task_issues.append('task receipt absent/different')
  taskreceipt=dest/'driver-manifest.json'
  if not taskreceipt.exists() or sha(taskreceipt)!=task['driver_manifest_sha256']:task_issues.append('driver receipt absent/different')
  source_receipt=dest/'source.sha256'
  if not source_receipt.exists() or source_receipt.read_text().strip()!=task['sha256']:task_issues.append('source receipt absent/different')
  for limit in task['limits']:
   for arm in arms(task):
    armroot=dest/str(limit)/arm;inv=read_json(armroot/'invocation.json',tolerant=True)
    terminal=isinstance(inv,dict) and isinstance(inv.get('exit_code'),int)
    execution='missing'
    if terminal:execution=inv.get('status') or ('ok' if inv['exit_code']==0 else 'timeout' if inv['exit_code']==124 else 'error')
    verification='not_verified';raw=None
    try:raw=audit(task,armroot,limit,arm)
    except (OSError,ValueError,KeyError,TypeError,IndexError) as error:raw={'status':'malformed_evidence','detail':str(error)}
    raw_status=raw['status'];key=audit_key(dict(task,limit=limit,arm=arm));expected_audit.add(key)
    independent=audit_rows.get(key)
    norms=normalized.get(str(Path(taskid)/str(limit)/arm),{})
    support_names={p.name for p in armroot.glob('support-*.ofn')}
    if raw_status=='correct':
     verification='verified'
     if independent is None:verification='audit_row_missing'
     elif independent.get('status')!='correct':verification='independent_audit_not_correct'
     elif independent.get('supports')!=raw.get('supports'):verification='audit_count_mismatch'
     if norms.keys()!=support_names or len(norms)!=raw.get('supports'):verification='normalization_missing_or_incomplete'
     if task_issues:verification='binding_incomplete'
     if issues:verification='source_integrity_error'
    elif raw_status not in ['missing','timeout','error','memout']:verification=raw_status
    raw_count=raw.get('supports');distinct=len(set(norms.values())) if norms else None
    enum=raw.get('enumeration_complete')
    enumeration=('censored_timeout' if execution=='timeout' else 'censored_memory' if execution=='memout' else 'complete' if enum in (True,'true') else 'bounded_or_unfinished' if enum in (False,'false') else 'unknown')
    finite_time=terminal and isinstance(inv.get('elapsed_s'),(int,float)) and math.isfinite(inv['elapsed_s']) and inv['elapsed_s']>0
    valid=verification=='verified' and raw_count and distinct and finite_time
    if limit>1 and distinct is not None and raw_count!=distinct:valid=False
    if limit>1 and enumeration=='bounded_or_unfinished' and distinct is not None and distinct<limit:valid=False
    row=dict(source=spec['label'],final_km=final,task_id=taskid,ontology=task['ontology'],query_id=task['query_id'],query_hash=task['query_hash'],input_sha256=task['sha256'],track=task['track'],repetition=task['repetition'],warmup=task['warmup'],limit=limit,arm=arm,mechanism=arm.split('-',1)[1],execution=execution,extraction_terminal=terminal,task_terminal=(dest/'COMPLETE').exists(),semantic_status=verification,raw_audit_status=raw_status,raw_support_count=raw_count,distinct_logical_supports=distinct,logical_support_family_sha256=hashlib.sha256(('\n'.join(sorted(set(norms.values())))+'\n').encode()).hexdigest() if norms else None,duplicate_occurrences=(raw_count-distinct) if raw_count is not None and distinct is not None else None,enumeration=enumeration,performance_eligible=bool(valid),wall_s=inv.get('elapsed_s') if terminal else None,first_internal_s=raw.get('first_s'),extraction_internal_s=raw.get('extraction_s'),peak_tree_rss_bytes=inv.get('sampled_peak_process_tree_rss_bytes') if terminal else None,driver_manifest_sha256=task['driver_manifest_sha256'],binding_issues=task_issues,output_path=str(armroot))
    rows.append(row)
 if set(audit_rows)-expected_audit:issues.append('unexpected audit rows: '+str(len(set(audit_rows)-expected_audit)))
 if issues:
  for row in rows:row['performance_eligible']=False
 panel=read_json(root/'panel-status.json',[])
 for p in panel:
  p['source']=spec['label'];p['fragment']='DL+rules' if p['ontology'] in ['to','uberon'] else 'pure_DL' if p['ontology'] in ['mro','zfa','mfomd'] else 'EL'
 return dict(spec=spec,final=final,rows=rows,issues=issues,artifacts=artifacts,panel=panel,cases=case_inventory,manifest=manifest)


def render(config,out):
 out.mkdir(parents=True,exist_ok=True)
 sources=[evidence_source(s) for s in config['sources']]+[evidence_source(s,True) for s in config.get('km_final_sources',[])]
 rows=[r for s in sources for r in s['rows']];issues=[dict(source=s['spec']['label'],detail=i) for s in sources for i in s['issues']]
 labels=[s['spec']['label'] for s in sources]
 if len(set(labels))!=len(labels):issues.append(dict(source='configuration',detail='duplicate source labels'))
 base_cases={};final_cases={}
 for source in sources:
  target=final_cases if source['spec'] in config.get('km_final_sources',[]) else base_cases
  for key,task in source['cases'].items():
   if key in target:issues.append(dict(source=source['spec']['label'],detail='duplicate case across sources '+str(key)))
   target[key]=(task,source)
 expected_tasks=config.get('expected_baseline_tasks',300)
 if len(base_cases)!=expected_tasks:issues.append(dict(source='baseline',detail=f'expected {expected_tasks} frozen tasks, found {len(base_cases)}'))
 cohorts=defaultdict(set)
 for key in base_cases:cohorts[key[:-1]].add(key[-1])
 for key,reps in cohorts.items():
  if reps!=set(range(6)):issues.append(dict(source='baseline',detail='incomplete repetition cohort '+str(key)))
 if config.get('km_final_sources'):
  missing=set(base_cases)-set(final_cases);extra=set(final_cases)-set(base_cases)
  if missing or extra:issues.append(dict(source='final-KM',detail=f'final rerun case mismatch: missing={len(missing)} extra={len(extra)}'))
  for key in set(base_cases)&set(final_cases):
   _,base=base_cases[key];_,final=final_cases[key]
   for suffix in ['/justification_run.py','/JustificationBenchmark.java','/classifier-hermit.jar']:
    left=file_hashes(base['manifest'],suffix);right=file_hashes(final['manifest'],suffix)
    if len(left)!=1 or left!=right:issues.append(dict(source=final['spec']['label'],detail='timing protocol differs: '+suffix));break
 # Optional whole-arm corrections retain the original archive and replace only
 # the comparison selection, never individual failures or warmup repetitions.
 corrections=[];by_label={s['spec']['label']:s for s in sources};original_by_label=dict(by_label);replaced=set()
 for spec in config.get('common_corrections',[]):
  correction=evidence_source(spec);corrections.append(correction)
  original=original_by_label.get(spec.get('replaces'))
  target=(spec.get('replaces'),spec.get('correction_arm','km-common'))
  if original is None or target in replaced:
   issues.append(dict(source=spec['label'],detail='missing or duplicate correction target'))
  else:
   replaced.add(target);correction['final']=original['final']
   for row in correction['rows']:row['final_km']=original['final']
   for problem in justification_corrections.validate(original,correction):
    issues.append(dict(source=spec['label'],detail=problem))
  issues.extend(dict(source=spec['label'],detail=i) for i in correction['issues'])
  if spec['label'] in by_label:issues.append(dict(source=spec['label'],detail='duplicate correction label'))
  by_label[spec['label']]=correction
 corrected_arms={s['spec'].get('correction_arm','km-common') for s in corrections}
 expected_replacements={(s['spec']['label'],arm) for s in sources for arm in corrected_arms
                        if any(arm in arms(task) for task in s['cases'].values())}
 if corrections and replaced!=expected_replacements:
  issues.append(dict(source='corrections',detail='each corrected arm must cover every original panel containing that arm'))
 sources+=corrections;rows=[r for source in sources for r in source['rows']]
 justification_corrections.select(sources,corrections)
 if issues:
  for row in rows:row['performance_eligible']=False
 grouped=defaultdict(list)
 for row in rows:
  if not row['warmup']:grouped[tuple(row[k] for k in ['source','ontology','query_hash','track','limit','arm'])].append(row)
 cases=[]
 for key,group in sorted(grouped.items()):
  good=[r for r in group if r['performance_eligible']]
  complete_reps={r['repetition'] for r in group}=={1,2,3,4,5}
  stats=spread([r['wall_s'] for r in good])
  cases.append(dict(zip(['source','ontology','query_hash','track','limit','arm'],key),scheduled=len(group),expected_measured_reps=5,repetition_manifest_complete=complete_reps,terminal=sum(r['extraction_terminal'] for r in group),verified=sum(r['semantic_status']=='verified' for r in group),eligible=len(good),execution_counts=dict(Counter(r['execution'] for r in group)),semantic_counts=dict(Counter(r['semantic_status'] for r in group)),enumeration_counts=dict(Counter(r['enumeration'] for r in group)),**{'wall_'+k:v for k,v in stats.items()}))
 summaries=[]
 for key in sorted({tuple(r[k] for k in ['source','track','limit','arm']) for r in rows if not r['warmup']}):
  group=[r for r in rows if not r['warmup'] and tuple(r[k] for k in ['source','track','limit','arm'])==key]
  summaries.append(dict(zip(['source','track','limit','arm'],key),scheduled=len(group),extraction_terminal=sum(r['extraction_terminal'] for r in group),verified=sum(r['semantic_status']=='verified' for r in group),eligible=sum(r['performance_eligible'] for r in group),execution_counts=dict(Counter(r['execution'] for r in group)),semantic_counts=dict(Counter(r['semantic_status'] for r in group)),enumeration_counts=dict(Counter(r['enumeration'] for r in group))))
 # Only compare matched end-to-end process wall times; no cross-API internal timings.
 pairs=[];index={}
 for row in rows:
  if row['warmup'] or not row['comparison_selected']:continue
  key=tuple(row[k] for k in ['ontology','query_hash','input_sha256','track','repetition','limit','arm'])
  if row['arm'].startswith('km-') and config.get('km_final_sources') and not row['final_km']:continue
  index[key]=row
 for key,left in sorted(index.items()):
  if not left['arm'].startswith('km-'):continue
  for peer in ['hermit-common','jfact-common','openllet-common','konclude-common','elk-common','whelk-common','hermit-library','jfact-library','openllet-library']:
   right=index.get(key[:-1]+(peer,))
   if not right:continue
   compatible=left['mechanism']==right['mechanism'] or left['arm']=='km-native'
   support_compatible=left['limit']==1 or (left['enumeration']=='complete' and right['enumeration']=='complete' and left['distinct_logical_supports']==right['distinct_logical_supports'] and left['logical_support_family_sha256']==right['logical_support_family_sha256']) or (left['distinct_logical_supports']==left['limit']==right['distinct_logical_supports'])
   eligible=compatible and support_compatible and left['performance_eligible'] and right['performance_eligible'] and not issues
   pairs.append(dict(ontology=left['ontology'],query_hash=left['query_hash'],track=left['track'],repetition=left['repetition'],limit=left['limit'],km_arm=left['arm'],peer_arm=peer,km_source=left['source'],peer_source=right['source'],km_harness_revision=left['harness_revision'],peer_harness_revision=right['harness_revision'],paired_eligible=bool(eligible),reason='matched' if eligible else 'incomplete, invalid, unequal support target, or protocol mismatch',peer_over_km_wall_ratio=(right['wall_s']/left['wall_s']) if eligible else None))
 pair_cases=defaultdict(list)
 for pair in pairs:pair_cases[tuple(pair[k] for k in ['ontology','query_hash','track','limit','km_arm','peer_arm'])].append(pair)
 pair_groups=defaultdict(list)
 for key,group in pair_cases.items():
  good=[r for r in group if r['paired_eligible']]
  complete={r['repetition'] for r in good}=={1,2,3,4,5} and len(good)==5
  pair_groups[key[2:]].append(statistics.median(r['peer_over_km_wall_ratio'] for r in good) if complete else None)
 paired_summary=[]
 for key,values in sorted(pair_groups.items()):
  stats=spread([v for v in values if v is not None])
  paired_summary.append(dict(zip(['track','limit','km_arm','peer_arm'],key),expected_cases=len(values),complete_five_rep_cases=stats['n'],**{'case_ratio_'+k:v for k,v in stats.items() if k!='n'}))
 for name,data in [('attempts',rows),('cases',cases),('coverage',summaries),('paired-wall',pairs),('paired-summary',paired_summary),('artifacts',[r for s in sources for r in s['artifacts']]),('panel',[r for s in sources if not s['final'] for r in s['panel']]),('runtime-bindings',[dict(source=s['spec']['label'],artifact_path=p,sha256=h) for s in sources for p,h in s['manifest'].items()]),('integrity',issues)]:table(out/(name+'.tsv'),data)
 terminal=sum(r['extraction_terminal'] for r in rows);semantic=sum(r['semantic_status']=='verified' for r in rows)
 completed=terminal==len(rows) and all(r['task_terminal'] for r in rows) and not issues
 measured=sum(not r['warmup'] for r in rows)
 text=['# Justification comparison','',('VALIDATION ONLY: fixture/partial evidence; not main performance.' if config.get('validation_only') else 'Frozen benchmark matrix; all scheduled outcomes remain in the denominator.'),'',f'Scheduled: {len(rows)} attempts ({measured} measured, {len(rows)-measured} warmups). Extraction terminal: {terminal}/{len(rows)}. Independently verified with normalization and bindings: {semantic}/{len(rows)}.',f'Matrix execution complete: {completed}. Integrity issues: {len(issues)}. Semantic success is separate from execution completeness.','', '| Source | Track | Bound | Arm | Scheduled measured | Terminal | Verified | Timing eligible |','|---|---|---:|---|---:|---:|---:|---:|']
 for s in summaries:text.append('| '+' | '.join(str(s[k]) for k in ['source','track','limit','arm','scheduled','extraction_terminal','verified','eligible'])+' |')
 text+=['','## Paired process wall times','', 'Each ratio is peer wall time divided by KM wall time. Values above1 favor KM on the stated matched cases. A case enters only if all five measured repetitions have compatible, independently verified outputs. The summary uses the median of these five-repetition case medians; incomplete cases stay in the denominator.','', '| Track | Bound | KM mechanism | Peer mechanism | Complete cases / expected | Median ratio | Case ratio IQR |','|---|---:|---|---|---:|---:|---:|']
 for p in paired_summary:
  median='NA' if p['case_ratio_median'] is None else format(p['case_ratio_median'],'.4g')
  iqr='NA' if p['case_ratio_iqr'] is None else format(p['case_ratio_iqr'],'.4g')
  text.append(f"| {p['track']} | {p['limit']} | {p['km_arm']} | {p['peer_arm']} | {p['complete_five_rep_cases']} / {p['expected_cases']} | {median} | {iqr} |")
 text+=['','Per-case latency median, min/max, IQR and MAD are in [cases.tsv](cases.tsv); all outcomes and support counts are in [attempts.tsv](attempts.tsv). Runtime and source hashes are in [runtime-bindings.tsv](runtime-bindings.tsv).','', '## Preparation outcomes','', '| Source | Ontology | Fragment | Status |','|---|---|---|---|']
 for s in sources:
  if s['final']:continue
  for p in s['panel']:text.append('| '+' | '.join(str(p[k]) for k in ['source','ontology','fragment','status'])+' |')
 text+=['','## Reading the files','', 'Only repetitions 1–5 enter case dispersion and paired ratios; repetition 0 is a filesystem-cache warmup in a fresh process. Full ontologies and STAR modules, extraction mechanisms and bounds remain separate. Limit 1 end-to-end wall time measures user-facing first-justification latency; Java internal first/extraction times are retained only as diagnostic columns and are never mixed with native wall time.','', 'Timeouts, resource failures, errors, missing attempts and verification failures are counted explicitly. A timeout is censored at the recorded wall limit, never a zero-time or zero-support success. False positive-query responses are ineligible. Unknown library enumeration is never treated as complete. Native occurrence counts and normalized distinct logical-support counts remain separate; duplicate inflation excludes bounded-enumeration timing comparisons.','', 'Per-case TSV records median, min/max, IQR and median absolute deviation over eligible repetitions, alongside the required five-repetition denominator. Paired ratios use only matching query/source/repetition/track/bound and compatible completed support targets. They compare common extractors, or native KM against the named service; they do not pool mechanisms. No pooled conditional median is presented as an overall speed winner.','', 'artifacts.tsv lists frozen task, audit, normalization and driver-receipt hashes. Driver manifests bind source code, compiled classes, runtime JARs and native binaries. Matrix completeness does not certify calculus correctness or establish a release gate.']
 if corrections:
  text+=['','## Corrected common-driver cohort','',
   'The archive includes every original attempt plus the full stream-v4 common-driver rerun. comparison_selected identifies the fixed-size comparison cohort; original common-driver attempts remain visible but cannot substitute for missing or failed corrected attempts.',
   'The exact adapter patch drains subprocess stdout before JSON parsing. The declared correction arms identify affected KM or Konclude common-driver cohorts; all other peer and native runs are unchanged. Corrected runs occurred later without inter-arm rotation; cache and shared-resource contention can affect timing. Paired rows identify both harness revisions. These are separate measurement cohorts, not extra interchangeable repetitions.']
 (out/'comparison.md').write_text('\n'.join(text)+'\n')
 report=dict(attempts=len(rows),measured=measured,terminal=terminal,verified=semantic,matrix_execution_complete=completed,integrity_issues=issues,validation_only=config.get('validation_only',False))
 (out/'config.snapshot.json').write_text(json.dumps(config,indent=2,sort_keys=True)+'\n')
 report['comparison_selected_attempts']=sum(r['comparison_selected'] for r in rows)
 report['correction_validator_sha256']=sha(Path(justification_corrections.__file__))
 report['config_sha256']=sha(out/'config.snapshot.json')
 report['renderer_sha256']=sha(__file__)
 report['raw_auditor_sha256']=sha(Path(__file__).with_name('audit_justification_main.py'))
 (out/'summary.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('config',type=Path);p.add_argument('output',type=Path);a=p.parse_args();print(json.dumps(render(read_json(a.config),a.output)))
