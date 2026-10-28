import subprocess,json,os,sys
S=sys.argv[1]; seeds=range(int(sys.argv[2]),int(sys.argv[3])); out=open(sys.argv[4],'a')
import concurrent.futures as cf
def km(p,route):
    env={k:v for k,v in os.environ.items() if not k.startswith("KM_")}
    if route!="auto": env["KM_ROUTE"]=route
    try: o=subprocess.run(["timeout","60",S+"/km.h7","classify","--lines",p],capture_output=True,text=True,env=env).stdout
    except Exception as e: return None
    cons=None;subs=set();uns=set()
    for l in o.splitlines():
        t=l.split("\t")
        if t[0].startswith("CONSISTENT"): cons=t[0].endswith("1")
        elif t[0]=="SUB": subs.add((t[1].lstrip(":"),t[2].lstrip(":")))
        elif t[0]=="UNSAT": uns.add(t[1].lstrip(":"))
    if cons is None: return None
    return cons,frozenset(s for s in subs if s[0] not in uns and s[1] not in uns),frozenset(uns)
def hermit(p):
    o=subprocess.run(["timeout","120","java","-cp",".:"+open(S+"/oracle/cp.txt").read().strip(),"Oracle",p],cwd=S+"/oracle",capture_output=True,text=True).stdout
    try: d=json.loads(o)
    except: return None
    uns=set(d["unsatisfiable"])
    return d["consistent"],frozenset((a,b) for a,b in d["subsumptions"] if a not in uns and b not in uns and a!=b),frozenset(uns)
def one(seed):
    p=f"{S}/sq/g{seed}.ofn"
    subprocess.run(["python3","-I",S+"/tools/gen_alc.py",str(seed),p])
    h=hermit(p)
    if h is None: return f"{seed} hermit-error"
    res=[]
    for r in ["seq_on","seq_off","auto"]:
        k=km(p,r)
        if k is None: res.append(f"{r}:ERR")
        elif k==h: res.append(f"{r}:ok")
        else:
            cons_d = "cons" if k[0]!=h[0] else ""
            res.append(f"{r}:WRONG(miss_sub={len(h[1]-k[1])},extra_sub={len(k[1]-h[1])},miss_unsat={len(h[2]-k[2])},extra_unsat={len(k[2]-h[2])}{cons_d})")
    return f"{seed} "+" ".join(res)
with cf.ThreadPoolExecutor(8) as ex:
    for line in ex.map(one, seeds):
        out.write(line+"\n"); out.flush()
