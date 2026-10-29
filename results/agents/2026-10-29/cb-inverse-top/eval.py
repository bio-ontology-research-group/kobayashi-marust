# usage: eval.py KM_BIN lo hi outfile [ENV=VAL ...]
# Adapted from results/agents/2026-10-28/bridge/eval.py: seed/gold dirs from env.
# SQ (optional first seed dir), SEEDS, GOLD, GEN (generator), ORACLE (dir).
import subprocess,json,os,sys,concurrent.futures as cf
SQ=os.environ.get("SQ",""); SEEDS=os.environ["SEEDS"]; GOLD=os.environ["GOLD"]
GEN=os.environ["GEN"]; ORACLE=os.environ["ORACLE"]
km_bin=sys.argv[1]; lo=int(sys.argv[2]); hi=int(sys.argv[3]); out=sys.argv[4]
extra=dict(a.split("=",1) for a in sys.argv[5:])
def path(seed):
    if SQ:
        p=f"{SQ}/g{seed}.ofn"
        if os.path.exists(p): return p
    p=f"{SEEDS}/g{seed}.ofn"
    if not os.path.exists(p): subprocess.run(["python3","-I",GEN,str(seed),p],check=True)
    return p
def gold(seed,p):
    g=f"{GOLD}/{seed}.json"
    if os.path.exists(g): return json.load(open(g))
    o=subprocess.run(["timeout","120","java","-cp",".:"+open(ORACLE+"/cp.txt").read().strip(),"Oracle",p],cwd=ORACLE,capture_output=True,text=True).stdout
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
    ms=sorted(h[1]-k[1]); es=sorted(k[1]-h[1])
    return f"{seed} WRONG(miss_sub={len(ms)},extra_sub={len(es)},miss_unsat={len(h[2]-k[2])},extra_unsat={len(k[2]-h[2])}) miss={ms} extra={es} mu={sorted(h[2]-k[2])} eu={sorted(k[2]-h[2])}"
with open(out,"w") as f, cf.ThreadPoolExecutor(int(os.environ.get("J","8"))) as ex:
    for line in ex.map(one, range(lo,hi)):
        f.write(line+"\n"); f.flush()
