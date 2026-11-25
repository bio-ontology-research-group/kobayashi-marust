import json,glob,collections as C,statistics as st
L=lambda d:{x['ontology']:x for f in glob.glob('data/'+d+'/chunks/*.json') for x in json.load(open(f))['outcomes']}
ox,km,kc=L('heldout-oxidowl-56392968'),L('heldout-rc6-pair56301530'),L('heldout-konclude5-56301531')
d=json.load(open('data/diagnosis.json'))
done={o for o in ox if ox[o]['cls']['status']=='executed_unvalidated'}
aud_ok={o for o in done if any(v.get('agreement') is True for v in ox[o].get('audit',{}).get('taxonomy',{}).values())}
agree={o for o,v in d.items() if 'classes' in v and v['missing_pairs']==0 and v['extra_pairs']==0}
refinc={o for o,v in d.items() if v.get('reference_consistent') is False}
print('rescued among diag-not-aud',[(o,d[o]['rescued_iri_keys'],d[o]['unknown_keys']) for o in sorted(agree-aud_ok)])
ok=agree|aud_ok
wrong=done-ok-refinc
miss={o for o in wrong if d[o]['missing_pairs']}; ext={o for o in wrong if d[o]['extra_pairs']}
print('done',len(done),'refincons',len(refinc),'correct',len(ok),'wrong',len(wrong),'missing',len(miss),'extra',len(ext),'extra only',len(ext-miss))
fr=sorted(d[o]['missing_pairs']/d[o]['ref_pairs'] for o in miss if d[o]['ref_pairs']); print('missing share median',st.median(fr), 'q1',fr[len(fr)//4],'q3',fr[3*len(fr)//4])
print('refincons k verdict',C.Counter(json.dumps(ox[o].get('k_verdict')) for o in refinc))
kd=[o for o in ox if ox[o]['k']['status']=='executed_unvalidated']
def ref(o):
    r=set(ox[o]['reference_consistent'].values()); return r.pop() if len(r)==1 else 'mixed'
print('k finished',len(kd), C.Counter((ox[o]['k_verdict'],ref(o)) for o in kd))
print('ku finished',sum(ox[o]['ku']['status']=='executed_unvalidated' for o in ox))
kmok={o for o in km if km[o]['verified_solved']}
S=ok&kmok; print('common',len(S), 'ok not km', ok-kmok)
for n,D,key in(('KM',km,None),('KC',kc,None),('OX',ox,'cls')):
    g=lambda o:(D[o][key] if key else D[o])
    w=[g(o)['wall_s'] for o in S]; m=[g(o)['peak_bytes']/2**20 for o in S]
    print(n,'mean %.2f median %.3f | mem median %.1f mean %.1f'%(st.mean(w),st.median(w),st.median(m),st.mean(m)))
print('KM faster',sum(km[o]['wall_s']<ox[o]['cls']['wall_s'] for o in S),'smaller',sum(km[o]['peak_bytes']<ox[o]['cls']['peak_bytes'] for o in S))
to=[o for o in ox if ox[o]['cls']['status']=='timeout']
print('timeouts',len(to),'of which km verified',sum(o in kmok for o in to),'km median s on them',st.median(km[o]['wall_s'] for o in to if o in kmok))
print('cls status',C.Counter(ox[o]['cls']['status'] for o in ox))
json.dump({'correct':sorted(ok),'wrong':sorted(wrong),'reference_inconsistent':sorted(refinc)},open('data/oxidowl-verdicts.json','w'))
