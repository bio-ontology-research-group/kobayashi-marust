#!/usr/bin/env python3
"""Render audited incremental evidence without changing any running harness.

--audit LABEL=PATH may repeat (baseline and supplement may share a label).
Future KM-only audits use audit_incremental.py's schema: cases/repetitions/arms,
manifest_sha256, expected_states, full state hashes, measurements and receipts.
Independent fresh references can come from another supplied audit but must have
an identical case, manifest hash and complete state vector. Optional scheduler
receipts are TSV or sacct -P with JobID,State,ExitCode columns; no remote polling.
"""
import argparse
from collections import Counter, defaultdict
import csv
import hashlib
import json
import math
from pathlib import Path
import statistics

PURE_DL={'mfomd','zfa','mro'}
EL={'mmo','hao','vto'}
RULES={'to','uberon'}
TERMINAL={'COMPLETED','FAILED','CANCELLED','TIMEOUT','OUT_OF_MEMORY','NODE_FAIL','PREEMPTED','BOOT_FAIL','DEADLINE','REVOKED'}
CONTROL={'additions','deletions','rbox','abox','equality','disjunction'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def stratum(case):
    name=case.split('-n')[0]
    if name in PURE_DL:return 'pure_OWL2DL'
    if name in EL:return 'OWL2EL'
    if name in RULES:return 'DL_plus_rules_stress'
    if name in CONTROL:return 'analytic_controls'
    return 'unverified_profile'

def vector(arm,expected):
    if not arm.get('complete'):return None
    states=arm.get('states',{})
    if set(states)!={str(i) for i in range(expected)}:return None
    result=[]
    for i in range(expected):
        s=states[str(i)];h=s.get('sha256','')
        if s.get('issues') or len(h)!=64 or any(c not in '0123456789abcdef' for c in h):return None
        result.append(h)
    return tuple(result)

def job_keys(m):
    values=[]
    if m.get('slurm_array_job') and m.get('slurm_array_task') is not None:
        values.append(str(m['slurm_array_job'])+'_'+str(m['slurm_array_task']))
    if m.get('slurm_job'):values.append(str(m['slurm_job']))
    return values

def scheduler_records(paths):
    records={}
    for path in paths:
        text=path.read_text();delimiter='\t' if '\t' in text.splitlines()[0] else '|'
        for row in csv.DictReader(text.splitlines(),delimiter=delimiter):
            job=row.get('JobIDRaw',row.get('JobID',row.get('job_id')))
            state=row.get('State',row.get('state','')).split()[0].rstrip('+')
            if job:records[job.strip()]={'state':state,'exit_code':row.get('ExitCode',row.get('exit_code','')),'source':str(path),'source_sha256':sha(path)}
    return records

def load_audits(specs):
    loaded=[];attempts=[];seen=set()
    for spec in specs:
        label,name=spec.split('=',1);path=Path(name);audit=json.loads(path.read_text())
        if not isinstance(audit.get('cases'),dict):raise ValueError('not an incremental audit: '+name)
        origin={'label':label,'path':str(path),'sha256':sha(path),'audit':audit}
        loaded.append(origin)
        for case,c in audit['cases'].items():
            for rep,r in c.get('repetitions',{}).items():
                for key,a in r['arms'].items():
                    reasoner,arm=key.split('/',1);unique=(label,case,str(rep),reasoner,arm)
                    if unique in seen:raise ValueError('duplicate labelled attempt: '+repr(unique))
                    seen.add(unique)
                    attempts.append(dict(label=label,case=case,rep=str(rep),reasoner=reasoner,arm=arm,
                        expected=c['expected_states'],manifest=c['manifest_sha256'],data=a,origin=origin,
                        phase=audit['phase'],stratum=stratum(case)))
    return loaded,attempts

def reference_index(attempts):
    candidates=defaultdict(lambda:defaultdict(list))
    for a in attempts:
        if a['reasoner'] not in ('hermit','jfact') or a['arm']!='fresh':continue
        v=vector(a['data'],a['expected'])
        if v is not None:
            key=(a['case'],a['manifest'],a['expected'])
            candidates[key][a['reasoner']].append((v,a))
    references={}
    for key,by_reasoner in candidates.items():
        h=by_reasoner['hermit'];j=by_reasoner['jfact']
        # A disagreement among any completed fresh repetition is not hidden by
        # selecting a convenient agreeing pair.
        vectors={v for v,_ in h+j}
        if h and j and len(vectors)==1:
            references[key]=(next(iter(vectors)),[h[0][1],j[0][1]])
    return references

def finite(value):
    return isinstance(value,(int,float)) and math.isfinite(value) and value>=0

def render(specs,out,slurm_paths=(),expected_repetitions=5,failure_paths=()):
    loaded,attempts=load_audits(specs);references=reference_index(attempts)
    failure_entries={}
    for path in failure_paths:
        sidecar=json.loads(path.read_text());sidecar_sha=sha(path)
        for entry in sidecar['entries']:
            key=tuple(entry[k] for k in ('label','audit_sha256','case','repetition','reasoner','arm'))
            if key in failure_entries:raise ValueError('duplicate failure sidecar entry')
            failure_entries[key]=(entry,sidecar_sha)
    scheduler=scheduler_records(slurm_paths);groups=defaultdict(list)
    for a in attempts:groups[(a['label'],a['case'],a['reasoner'])].append(a)
    inferred={}
    for key,items in groups.items():
        ids={job_keys(a['data'].get('measurement',{}))[0] for a in items if job_keys(a['data'].get('measurement',{}))}
        if len(ids)==1:inferred[key]=next(iter(ids))
    rows=[];provenance=[]
    for a in attempts:
        d=a['data'];m=d.get('measurement',{});raw=d.get('status','missing')
        keys=job_keys(m) or [inferred.get((a['label'],a['case'],a['reasoner']),'')]
        scheduled=next((scheduler[k] for k in keys if k in scheduler),{})
        finalized='rc' in m and m['rc'] is not None and raw not in ('running','missing','unknown','invalid_measurement')
        terminal=finalized or scheduled.get('state') in TERMINAL
        effective=raw
        if not finalized and terminal:
            effective={'TIMEOUT':'timeout','OUT_OF_MEMORY':'memout','COMPLETED':'incomplete_output'}.get(scheduled['state'],'scheduler_'+scheduled['state'].lower())
        v=vector(d,a['expected']);reference=references.get((a['case'],a['manifest'],a['expected']))
        correct=bool(v is not None and reference and v==reference[0] and finalized and raw=='ok')
        mismatch=bool(v is not None and reference and v!=reference[0])
        if mismatch:verdict='incorrect'
        elif correct:verdict='verified_correct'
        elif any('analytic_' in x or 'signature_issue' in x for x in d.get('issues',[])):verdict='incorrect_or_invalid_output'
        elif effective!='ok':verdict=effective
        else:verdict='unverified'
        failure_kind='';failure_sidecar=''
        sidecar=failure_entries.get((a['label'],a['origin']['sha256'],a['case'],a['rep'],a['reasoner'],a['arm']))
        if sidecar:
            entry,failure_sidecar=sidecar
            if entry.get('measurement_sha256','')!=d.get('measurement_sha256','') or entry['reported_status']!=raw:
                raise ValueError('failure sidecar is not bound to the audited measurement')
            failure_kind=entry['classification']
            if not correct and raw!='ok' and failure_kind in ('timeout','unsupported','parse_error'):
                findings=entry.get('findings',[])
                if not findings or {f['kind'] for f in findings}!={failure_kind}:raise ValueError('missing or conflicting direct cause evidence')
                verdict=failure_kind
        warmup=a['rep']=='warmup'
        reuse=d.get('km_receipt_summary',{});strategies=reuse.get('strategies',{});counts=reuse.get('reuse',{})
        row=dict(label=a['label'],phase=a['phase'],stratum=a['stratum'],case=a['case'],reasoner=a['reasoner'],arm=a['arm'],repetition=a['rep'],warmup=warmup,
            terminal=terminal,operational_status=effective,raw_status=raw,failure_kind=failure_kind,failure_sidecar_sha256=failure_sidecar,scheduler_state=scheduled.get('state',''),verdict=verdict,correct_complete=correct,
            expected_states=a['expected'],completed_states=m.get('completed_states',0),wall_s=m.get('wall_s',''),peak_mib=m.get('peak_mib',''),
            history_timeout_s=m.get('history_timeout_s',''),state_timeout_s=m.get('state_timeout_s',''),memcap_mib=m.get('memcap_mib',''),
            runtime_sha256=m.get('runtime_sha256',''),manifest_sha256=a['manifest'],audit_sha256=a['origin']['sha256'],measurement_sha256=d.get('measurement_sha256',''),
            exact_rebuild_count=strategies.get('exact_rebuild',0),el_delta_count=strategies.get('el_delta',0),meaningful_incremental_updates=counts.get('meaningful_incremental_update',0),
            reused_fixpoints=counts.get('reused_fixpoint',0),retained_states_sum=counts.get('retained_states',0),reused_edges_sum=counts.get('reused_edges',0),
            receipt_strategies=json.dumps(strategies,sort_keys=True),issues=';'.join(d.get('issues',[])),
            oracle_audits=';'.join(x['origin']['sha256']+':'+x['reasoner']+':'+x['rep'] for x in reference[1]) if reference else '',
            intervals_json=json.dumps(d.get('timings',{}).get('intervals',{}),sort_keys=True))
        rows.append(row);a['row']=row
        provenance.append(dict(label=a['label'],case=a['case'],reasoner=a['reasoner'],arm=a['arm'],repetition=a['rep'],
            runtime_sha256=m.get('runtime_sha256',''),manifest_sha256=a['manifest'],audit_path=a['origin']['path'],audit_sha256=a['origin']['sha256'],
            measurement_sha256=d.get('measurement_sha256',''),harness_hashes=json.dumps(m.get('source_sha256',{}),sort_keys=True),
            driver_build=json.dumps(m.get('driver_build'),sort_keys=True),slurm_ids=';'.join(keys),scheduler_receipt=json.dumps(scheduled,sort_keys=True)))
    summaries=[];grouped=defaultdict(list)
    for row in rows:
        if not row['warmup']:grouped[tuple(row[k] for k in ('label','phase','stratum','case','reasoner','arm'))].append(row)
    for key,items in sorted(grouped.items()):
        label,phase,s,case,reasoner,arm=key
        planned=expected_repetitions if phase=='measured' else len(items)
        valid=[r for r in items if r['correct_complete']]
        walls=[r['wall_s'] for r in valid if finite(r['wall_s'])]
        peaks=[r['peak_mib'] for r in valid if finite(r['peak_mib'])]
        summaries.append(dict(label=label,phase=phase,stratum=s,case=case,reasoner=reasoner,arm=arm,planned_attempts=planned,
            observed_attempts=len(items),terminal_attempts=sum(r['terminal'] for r in items),correct_complete_histories=len(valid),
            outcomes=json.dumps(dict(Counter(r['verdict'] for r in items)),sort_keys=True),
            correct_wall_n=len(walls),correct_wall_median_s=statistics.median(walls) if walls else '',correct_wall_min_s=min(walls) if walls else '',correct_wall_max_s=max(walls) if walls else '',
            correct_peak_median_mib=statistics.median(peaks) if peaks else '',correct_peak_max_mib=max(peaks) if peaks else '',
            observed_wall_s=sum(r['wall_s'] for r in items if finite(r['wall_s'])),
            exact_rebuild_count=sum(r['exact_rebuild_count'] for r in items),el_delta_count=sum(r['el_delta_count'] for r in items),
            meaningful_incremental_updates=sum(r['meaningful_incremental_updates'] for r in items),reused_fixpoints=sum(r['reused_fixpoints'] for r in items)))
    speedups=[];paired=defaultdict(dict)
    for a in attempts:
        if a['rep']!='warmup':paired[(a['label'],a['phase'],a['case'],a['rep'],a['reasoner'])][a['arm']]=a
    for key,arms in sorted(paired.items()):
        if not all(k in arms and arms[k]['row']['correct_complete'] for k in ('session','fresh')):continue
        session,fresh=arms['session'],arms['fresh']
        if session['manifest']!=fresh['manifest']:continue
        def add(interval,sv,fv):
            if finite(sv) and finite(fv) and sv>0:speedups.append(dict(label=key[0],phase=key[1],stratum=stratum(key[2]),case=key[2],repetition=key[3],reasoner=key[4],interval=interval,session_s=sv,fresh_s=fv,fresh_over_session=fv/sv))
        add('whole_process_history_wall_s',session['row']['wall_s'],fresh['row']['wall_s'])
        si=session['data'].get('timings',{}).get('intervals',{});fi=fresh['data'].get('timings',{}).get('intervals',{})
        for name in si.keys() & fi.keys():add('updates_only:'+name,si[name].get('update_sum_s'),fi[name].get('update_sum_s'))
    ratio_groups=defaultdict(list)
    for r in speedups:ratio_groups[tuple(r[k] for k in ('label','phase','stratum','case','reasoner','interval'))].append(r['fresh_over_session'])
    ratio_summaries=[dict(zip(('label','phase','stratum','case','reasoner','interval'),key),paired_n=len(values),median_fresh_over_session=statistics.median(values),min_fresh_over_session=min(values),max_fresh_over_session=max(values)) for key,values in sorted(ratio_groups.items())]
    out.mkdir(parents=True,exist_ok=False)
    def tsv(name,values,empty_fields):
        with (out/name).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=list(values[0]) if values else empty_fields,delimiter='\t');w.writeheader();w.writerows(values)
    tsv('attempts.tsv',rows,['label','case','verdict']);tsv('summary.tsv',summaries,['label','case']);tsv('paired-speedups.tsv',speedups,['label','case','reasoner','interval','fresh_over_session']);tsv('provenance.tsv',provenance,['label','audit_sha256'])
    tsv('paired-speedup-summary.tsv',ratio_summaries,['label','case','reasoner','interval','paired_n'])
    md=['# Incremental reasoning comparison','',
        'This report describes the supplied audited evidence. It does not establish release certification or completion of any missing experiments.', '',
        'Warmups are excluded from timing summaries. Times below are whole-process history wall times, including runtime startup, parsing, reasoning, canonicalization and output. They support an end-to-end service comparison, not an inference-only cross-interface speedup. Konclude starts a fresh process per state; the other fresh arms reconstruct reasoning state inside a persistent runtime.', '',
        'Java extract_s measures taxonomy extraction; hashing and writing signatures occur afterward and are included in whole-process wall time. KM canonicalize_s similarly excludes subsequent signature writing. Raw supervisor status remains in attempts.tsv; direct timeout/unsupported/parse-error evidence, when supplied, appears in separate failure_kind and verdict fields. A parser rejection is not automatically labelled unsupported.', '',
        'Each main history has 251 states and five planned measured repetitions. Reported timing uncertainty is the observed minimum–maximum range with sample count, not a confidence interval. Failed and unverified histories remain in every denominator; timing medians use only independently verified complete histories. Pilot/control inputs are explicitly labelled and do not count as main evaluation.', '',
        '| Evidence | Phase | Terminal attempts / planned (including warmup) | Measured correct / observed |',
        '|---|---|---:|---:|']
    coverage=[]
    for origin in loaded:
        subset=[r for r in rows if r['audit_sha256']==origin['sha256'] and r['label']==origin['label']]
        planned=origin['audit'].get('summary',{}).get('expected_arms',len(subset))
        if origin['audit']['phase']=='measured':
            declared_groups={(r['case'],r['reasoner'],r['arm']) for r in subset}
            planned=max(planned,len(declared_groups)*(expected_repetitions+1))
            wanted={'warmup',*(str(i) for i in range(expected_repetitions))}
            repetition_scope_complete=all(set(c.get('repetitions',{}))==wanted for c in origin['audit']['cases'].values())
        else:repetition_scope_complete=all(c.get('repetitions') for c in origin['audit']['cases'].values())
        terminal=sum(r['terminal'] for r in subset)
        measured=[r for r in subset if not r['warmup']]
        md.append('| %s | %s | %d / %d | %d / %d |'%(origin['label'],origin['audit']['phase'],terminal,planned,sum(r['correct_complete'] for r in measured),len(measured)))
        coverage.append(dict(label=origin['label'],audit_sha256=origin['sha256'],planned_attempts=planned,observed_attempts=len(subset),terminal_attempts=terminal,repetition_scope_complete=bool(repetition_scope_complete),execution_complete=terminal==planned and len(subset)==planned and bool(repetition_scope_complete)))
    md+=['','Execution completeness includes terminal errors, timeouts and unsupported attempts. Correct completion additionally requires complete outputs and equality to independently agreeing fresh HermiT and JFact references on exactly the same source-history manifest. Missing/stale measurements do not prove terminal execution; optional scheduler receipts can establish termination but cannot establish correct output.', '',
        'The pure DL panel is mfomd/zfa/mro, alongside EL mmo/hao/vto. TO and uberon retain their original denominators under DL+rules stress: they contain 25 and 3 SWRL rules respectively. Unknown profiles remain unverified.', '',
        '| Evidence / stratum | Case | Reasoner / arm | Terminal / planned | Correct / planned | Correct history wall median [min–max] s (n) | Correct peak median MiB | Outcomes |',
        '|---|---|---|---:|---:|---|---:|---|']
    for s in summaries:
        timing='—' if not s['correct_wall_n'] else '%.3g [%.3g–%.3g] (%d)'%(s['correct_wall_median_s'],s['correct_wall_min_s'],s['correct_wall_max_s'],s['correct_wall_n'])
        peak='—' if s['correct_peak_median_mib']=='' else '%.3g'%s['correct_peak_median_mib']
        md.append('| %s / %s | %s | %s / %s | %d / %d | %d / %d | %s | %s | %s |'%(s['label'],s['stratum'],s['case'],s['reasoner'],s['arm'],s['terminal_attempts'],s['planned_attempts'],s['correct_complete_histories'],s['planned_attempts'],timing,peak,s['outcomes']))
    md+=['','Konclude retained-session deletion/exchange is unsupported by the deployed OWLlink API. Only its fresh arm is planned; this capability limitation is explicit rather than a successful incremental result. JFact session discrepancies remain incorrect even when its fresh arm agrees with the independent reference.', '',
        'Paired speedups are fresh/session ratios only within one reasoner, one source history and one repetition, where both arms are independently correct. `paired-speedups.tsv` keeps whole-process history wall and each API interval separate; it never combines unlike Java inference and KM request/response intervals.', '',
        '| Evidence | Case | Reasoner | Verified wall-time pairs | Fresh/session median [min–max] |', '|---|---|---|---:|---:|']
    for r in ratio_summaries:
        if r['interval']=='whole_process_history_wall_s':md.append('| %s | %s | %s | %d | %.3g [%.3g–%.3g] |'%(r['label'],r['case'],r['reasoner'],r['paired_n'],r['median_fresh_over_session'],r['min_fresh_over_session'],r['max_fresh_over_session']))
    md+=['','Java session means an existing OWLReasoner object receives manager changes and flush calls; it does not prove retained inference. ELK and Whelk are enrolled only on the EL stratum. KM reuse evidence comes from its explicit receipts.', '', '| Evidence | Case | KM exact rebuilds | EL delta receipts | Meaningful updates | Reused fixpoints |', '|---|---|---:|---:|---:|---:|']
    for s in summaries:
        if s['reasoner']=='km' and s['arm']=='session':md.append('| %s | %s | %d | %d | %d | %d |'%(s['label'],s['case'],s['exact_rebuild_count'],s['el_delta_count'],s['meaningful_incremental_updates'],s['reused_fixpoints']))
    md+=['','Reuse totals cover observed measured-session receipts, including partial/incorrect attempts; they describe mechanism, not verified performance. `retained_backend` alone is not evidence of inference reuse.', '',
        'Downloads: [attempts](attempts.tsv), [summaries](summary.tsv), [paired speedups](paired-speedups.tsv), [speedup ranges](paired-speedup-summary.tsv), [source/runtime provenance](provenance.tsv).', '', '| Evidence | Audit SHA-256 | Runtime SHA-256 values |','|---|---|---|']
    for o in loaded:
        hashes=sorted({r['runtime_sha256'] for r in rows if r['audit_sha256']==o['sha256'] and r['runtime_sha256']})
        md.append('| %s | `%s` | %s |'%(o['label'],o['sha256'],', '.join('`'+h+'`' for h in hashes)))
    (out/'README.md').write_text('\n'.join(md).replace('—','not available')+'\n')
    report={'renderer_sha256':sha(Path(__file__)),'coverage':coverage,'inputs':[{k:v for k,v in o.items() if k!='audit'} for o in loaded],
            'failure_sidecars':[{'path':str(p),'sha256':sha(p)} for p in failure_paths],
            'scheduler_receipts':[{'path':str(p),'sha256':sha(p)} for p in slurm_paths],'expected_main_measured_repetitions':expected_repetitions,'release_certification_established':False}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return rows,summaries,speedups,report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--audit',action='append',required=True);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--slurm-receipts',type=Path,action='append',default=[]);p.add_argument('--expected-repetitions',type=int,default=5);p.add_argument('--failure-causes',type=Path,action='append',default=[])
    a=p.parse_args();render(a.audit,a.out,a.slurm_receipts,a.expected_repetitions,a.failure_causes)
