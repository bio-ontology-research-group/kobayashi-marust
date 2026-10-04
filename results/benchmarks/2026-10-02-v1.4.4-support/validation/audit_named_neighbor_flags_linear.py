"""Independent source-witness audit of reported anonymous components."""
import bisect, collections, hashlib, json, pathlib, re, sys
root=pathlib.Path('/ibex/scratch/projects/c2014/hohndor/km/v144-support-recovery-20261003')
lex=re.compile(r'<[^>]*>|"(?:\\.|[^"\\])*"|#[^\n]*|[()]|[^\s()]+')
results=[]
for row in json.loads((root/'named-neighbor-flag-inputs.json').read_text()):
    raw=pathlib.Path(row['path']).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==row['sha256']
    source=raw.decode()
    line_starts=[0]+[m.end() for m in re.finditer(r"\n",source)]
    prefixes=dict(re.findall(r'Prefix\(\s*([^\s=]*:)\s*=\s*<([^>]*)>\s*\)',source))
    def iri(s):
        if s.startswith('<'): return s[1:-1]
        if s.startswith('_:'): return s
        key,local=s.split(':',1)
        return prefixes[key+':']+local
    tokens=[(m.group(),m.start(),m.end()) for m in lex.finditer(source) if not m.group().startswith('#')]
    edges=collections.defaultdict(set); named=collections.defaultdict(dict)
    for i,(token,start,end) in enumerate(tokens):
        if token!='ObjectPropertyAssertion' or tokens[i+1][0]!='(': continue
        depth=1;j=i+2;args=[]
        while depth:
            t=tokens[j][0]
            if t=='(': depth+=1
            elif t==')': depth-=1
            if depth: args.append(t)
            j+=1
        # Remove leading axiom annotations as balanced expressions.
        while args and args[0]=='Annotation':
            d=0;k=1
            while k<len(args):
                if args[k]=='(': d+=1
                if args[k]==')':
                    d-=1
                    if d==0: break
                k+=1
            args=args[k+1:]
        if args[0]=='ObjectInverseOf':
            assert args[1]=='(' and args[3]==')' and len(args)==6
            prop,a,b=args[2],args[5],args[4]
        else:
            assert len(args)==3,args
            prop,a,b=args
        prop=iri(prop);a=iri(a);b=iri(b)
        aa=a.startswith('_:');bb=b.startswith('_:')
        if not (aa or bb): continue
        witness={'line':bisect.bisect_right(line_starts,start),'assertion':source[start:tokens[j-1][2]]}
        if aa and bb: edges[a].add(b);edges[b].add(a)
        elif aa or bb: named[a if aa else b][(prop,a,b)]=witness
    seed=re.search(r'tree containing (\S+) has',row['message']).group(1)
    component=set();todo=[seed]
    while todo:
        node=todo.pop()
        if node in component: continue
        component.add(node);todo.extend(edges[node]-component)
    degrees={n:len(named[n]) for n in sorted(component)}
    confirmed=all(d>1 for d in degrees.values())
    results.append({'ontology':row['ontology'],'sha256':row['sha256'],'confirmed':confirmed,'component':sorted(component),'named_assertion_counts':degrees,'witnesses':{n:list(named[n].values())[:2] for n in sorted(component)}})
report={'cases':len(results),'confirmed':sum(r['confirmed'] for r in results),'all_input_hashes_match':True,'results':results}
(root/('named-neighbor-flag-audit-'+sys.argv[1]+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='results'}))
assert report['confirmed']==report['cases']
