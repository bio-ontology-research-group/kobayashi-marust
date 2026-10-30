import json,glob,sys,collections,statistics as st,re
d=sys.argv[1]
rows=[]; inc=0
for f in glob.glob(d+'/*.json'):
    x=json.load(open(f)); rows+=x['outcomes']; inc+=x['status']!='complete'
by=collections.defaultdict(dict)
for r in rows: by[r['ontology']][r['policy']]=r
print('incomplete chunks',inc,'inputs',len(by))
pol=['v153','general']
for p in pol:
    rs=[x[p] for x in by.values() if p in x]; v=[r for r in rs if r['verified_solved']]
    t=[r['wall_s'] for r in v]
    print(p,'verified',len(v),'wrong',[r['ontology'] for r in rs if r.get('wrong')],'mean %.3f median %.3f'%(st.mean(t),st.median(t)))
both=[o for o,x in by.items() if all(p in x and x[p]['verified_solved'] for p in pol)]
m={p:(st.mean([by[o][p]['wall_s'] for o in both]),st.median([by[o][p]['wall_s'] for o in both])) for p in pol}
print('common',len(both),' '.join('%s mean %.3f median %.3f'%(p,*m[p]) for p in pol),'ratio mean %.3f median %.3f'%(m['general'][0]/m['v153'][0],m['general'][1]/m['v153'][1]))
lost=[o for o,x in by.items() if x['v153']['verified_solved'] and not x['general']['verified_solved']]
gained=[o for o,x in by.items() if x['general']['verified_solved'] and not x['v153']['verified_solved']]
print('lost',lost); print('gained',gained)
def route(r):
    rs=[m.group(1) for l in r['route_trace'] for m in [re.search(r'route=(\S+)',l)] if m]
    return rs[-1] if rs else '-'
for o in lost: print(' ',o,'v153',route(by[o]['v153']),'%.1f'%by[o]['v153']['wall_s'],'| general',route(by[o]['general']),by[o]['general']['measurement_status'],[l[:110] for l in by[o]['general']['route_trace'][-2:]])
agg=collections.defaultdict(lambda:[0,0.0,0.0])
for o in both:
    a=agg[(route(by[o]['v153']),route(by[o]['general']))]; a[0]+=1; a[1]+=by[o]['v153']['wall_s']; a[2]+=by[o]['general']['wall_s']
for k,a in sorted(agg.items(),key=lambda x:-(x[1][2]-x[1][1]))[:8]: print('  %-26s -> %-22s n=%4d delta=%+8.1f'%(k[0],k[1],a[0],a[2]-a[1]))
