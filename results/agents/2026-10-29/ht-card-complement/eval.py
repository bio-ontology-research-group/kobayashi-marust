# usage: eval.py KM_BIN SEEDDIR(lo) hi outfile [ENV=VAL ...]
# Generates g<seed>.ofn (if missing) with gen_alc.py, caches HermiT gold, runs KM on auto route.
import subprocess,json,os,sys,concurrent.futures as cf
S="/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch"
B=S+"/bridge"
km_bin=sys.argv[1]; lo=int(sys.argv[2]); hi=int(sys.argv[3]); out=sys.argv[4]
extra=dict(a.split("=",1) for a in sys.argv[5:])
def path(seed):
    p=f"{S}/sq/g{seed}.ofn"
    if os.path.exists(p): return p
    p=f"{B}/seeds/g{seed}.ofn"
    if not os.path.exists(p): subprocess.run(["python3","-I",S+"/tools/gen_alc.py",str(seed),p],check=True)
    return p
def gold(seed,p):
    pass
    g=f"{B}/gold/{seed}.json"
    if os.path.exists(g): return json.load(open(g))
    o=subprocess.run(["timeout","120","java","-cp",".:"+open(S+"/oracle/cp.txt").read().strip(),"Oracle",p],cwd=S+"/oracle",capture_output=True,text=True).stdout
    try: d=json.loads(o)
    except Exception: d=None
    json.dump(d,open(g,"w")); return d
def norm_h(d):
    uns=set(d["unsatisfiable"])
    return d["consistent"],frozenset((a,b) for a,b in d["subsumptions"] if a not in uns and b not in uns and a!=b),frozenset(uns)
def km(p):
    env={k:v for k,v in os.environ.items() if not k.startswith("KM_")}; env.update(extra)
    try: r=subprocess.run(["timeout","60",km_bin,"classify","--lines",p],capture_output=True,text=True,env=env)
    except Exception: return None,""
    cons=None;subs=set();uns=set()
    for l in r.stdout.splitlines():
        t=l.split("\t")
        if t[0].startswith("CONSISTENT"): cons=t[0].endswith("1")
        elif t[0]=="SUB": subs.add((t[1].lstrip(":"),t[2].lstrip(":")))
        elif t[0]=="UNSAT": uns.add(t[1].lstrip(":"))
    if cons is None: return None,r.stderr
    return (cons,frozenset(s for s in subs if s[0] not in uns and s[1] not in uns and s[0]!=s[1]),frozenset(uns)),r.stderr
def one(seed):
    p=path(seed); d=gold(seed,p)
    if d is None: return f"{seed} hermit-error"
    h=norm_h(d); k,err=km(p)
    if k is None: return f"{seed} ERR"
    if not h[0]: return f"{seed} "+("ok" if not k[0] else "WRONG(missed-inconsistency)")
    if not k[0]: return f"{seed} WRONG(spurious-inconsistency)"
    if k==h: return f"{seed} ok"
    return f"{seed} WRONG(miss_sub={len(h[1]-k[1])},extra_sub={len(k[1]-h[1])},miss_unsat={len(h[2]-k[2])},extra_unsat={len(k[2]-h[2])})"
with open(out,"w") as f, cf.ThreadPoolExecutor(int(os.environ.get("J","16"))) as ex:
    for line in ex.map(one, range(lo,hi)):
        f.write(line+"\n"); f.flush()
