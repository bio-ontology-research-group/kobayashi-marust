import json,sys
from collections import Counter
cnt=Counter(); ex={}
for path in sys.argv[1:]:
    try: d=json.load(open(path))
    except Exception: continue
    for c in d.get('clauses',[]):
        def has_ind(t):
            return t['kind']=='ind' or (t['kind']=='fun' and has_ind(t['arg']))
        g=[a for a in c['body'] if (a['kind']=='concept' and has_ind(a['term'])) or (a['kind']=='role' and (has_ind(a['source']) or has_ind(a['target']))) or (a['kind']=='eq' and (has_ind(a['left']) or has_ind(a['right'])))]
        if g:
            shape=('empty-head' if not c['head'] else 'head')+':'+','.join(sorted(a['kind'] for a in c['body']))+':allground='+str(len(g)==len(c['body']))
            cnt[shape]+=1; ex.setdefault(shape,(path,c))
for k,v in cnt.most_common(): print(v,k, ex[k][0].split('/')[-1]); 
for k,(p,c) in ex.items(): print(k, json.dumps(c)[:300])
