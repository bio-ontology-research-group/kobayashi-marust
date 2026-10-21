"""Compact observed receipts, without treating cached counters as new work."""
from collections import Counter
import hashlib,json
from pathlib import Path
FIELDS=['meaningful_incremental_update','reused_complete_answer','resumed_backend_states','reused_subjects','reused_index_axioms','cross_revision_compiled_axioms','reclassified_subjects','published_pairs']
ARMS=('candidate_retained','released_baseline_retained')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def summarize(rows):
    states=Counter();strategies=Counter();values=[[] for _ in FIELDS]
    for state,receipt in rows:
        states[state]+=1
        if receipt is None:continue
        if isinstance(receipt.get('strategy'),str):strategies[receipt['strategy']]+=1
        for i,field in enumerate(FIELDS):
            v=receipt.get(field)
            if type(v) in (bool,int,float):values[i].append(int(v) if type(v)==bool else v)
    return {'states':dict(states),'strategies':dict(strategies),
            'counter_ranges':[[len(v),min(v),max(v)] if v else None for v in values]}
def build(work):
    work=Path(work);index=json.loads((work/'cli-receipt-index.json').read_text());by_case={};bindings=[]
    for row in index:
        p=work/'cli-records'/row['path'].lstrip('/')
        assert sha(p)==row['sha256'],str(p)
        record=json.loads(p.read_text());by_case.setdefault(row['ontology'],{})[(row['arm'],row['repetition'])]=record
        bindings.append(row)
    result={'schema':'km-observed-reuse-per-revision-v1','counter_fields':FIELDS,
            'counter_range_format':'[observations,minimum,maximum]; null means unavailable, never inferred as zero; boolean values encoded 0/1',
            'interpretation':'Strategies and counters are observations, not a universal reasoning-reuse claim. full_classify remains explicit; compiler/index reuse may accompany full classification. Cached OWLAPI native receipts are not counted as new work.',
            'cli_raw_record_bindings':bindings,'paths':{'cli':[],'owlapi':[]}}
    for ontology,records in sorted(by_case.items()):
        for revision in range(9):
            entry={'ontology':ontology,'revision':revision,'arms':{}}
            for arm in ARMS:
                observations=[]
                for repetition in range(5):
                    record=records[(arm,repetition)];stages={s['revision']:s for s in record['revisions']};s=stages.get(revision,{})
                    receipt=s.get('reuse_receipt')
                    observations.append(('new_receipt',receipt) if s.get('engine_status')=='ok' and isinstance(receipt,dict) and receipt else ('failed_or_unavailable',None))
                entry['arms'][arm]=summarize(observations)
            result['paths']['cli'].append(entry)
    for p in sorted((work/'records/owlapi').glob('*/panel/panel.json')):
        panel=json.loads(p.read_text());records={(a['arm'],a['repetition']):a['measurement'] for a in panel['attempts']};ontology=panel['attempts'][0]['fixture_id']
        for revision in range(9):
            entry={'ontology':ontology,'revision':revision,'arms':{}}
            for arm in ARMS:
                observations=[]
                for repetition in range(5):
                    record=records[(arm,repetition)];stages={s['revision']:s for s in record['revisions']};worker=stages.get(revision,{}).get('worker',{});receipt=worker.get('native_receipt')
                    if worker.get('native_receipt_updated') is True and isinstance(receipt,dict) and receipt:
                        observations.append(('new_receipt',receipt))
                    elif worker.get('public_noop_flush') is True:
                        observations.append(('public_noop_flush',None))
                    else:observations.append(('failed_or_unchanged_or_unavailable',None))
                entry['arms'][arm]=summarize(observations)
            result['paths']['owlapi'].append(entry)
    return result

def label(entry):
    parts=[f'{strategy} ({count}/5)' for strategy,count in sorted(entry['strategies'].items())]
    parts.extend(f'{state} ({count}/5)' for state,count in sorted(entry['states'].items()) if state!='new_receipt')
    return '; '.join(parts) or 'unavailable'
