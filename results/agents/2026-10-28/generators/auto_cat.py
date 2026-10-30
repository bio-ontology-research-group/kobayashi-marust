import subprocess,json,os,sys,re
S=sys.argv[1]
seeds=[l.split()[0] for l in open(S+"/sq/res.txt") if "auto:WRONG" in l]
def hermit(p):
    o=subprocess.run(["timeout","120","java","-cp",".:"+open(S+"/oracle/cp.txt").read().strip(),"Oracle",p],cwd=S+"/oracle",capture_output=True,text=True).stdout
    return json.loads(o)
def km(p,env_extra):
    env={k:v for k,v in os.environ.items() if not k.startswith("KM_")}; env.update(env_extra)
    o=subprocess.run(["timeout","60",S+"/km.h7","classify","--lines",p],capture_output=True,text=True,env=env).stdout
    cons=None;subs=set();uns=set()
    for l in o.splitlines():
        t=l.split("\t")
        if t[0].startswith("CONSISTENT"): cons=t[0].endswith("1")
        elif t[0]=="SUB": subs.add((t[1].lstrip(":"),t[2].lstrip(":")))
        elif t[0]=="UNSAT": uns.add(t[1].lstrip(":"))
    return cons,subs,uns
from collections import Counter
cats=Counter()
for s in seeds:
    p=f"{S}/sq/g{s}.ofn"; h=hermit(p)
    k=km(p,{})
    nst=km(p,{"KM_ROUTE":"manual","KM_MECHANISM":"portfolio","KM_HT_ONLY":"certified","KM_ABSORB":"1","KM_TRIGGER_ABSORB":"1","KM_NO_SOURCE_TBOX":"1"})
    if not h["consistent"]:
        cat = "missed-inconsistency" if k[0] else "ok(inconsistent)"
    else:
        hu=set(h["unsatisfiable"]); hs={tuple(x) for x in h["subsumptions"] if x[0] not in hu and x[1] not in hu}
        ks={x for x in k[1] if x[0] not in k[2] and x[1] not in k[2]}
        cat=[]
        if k[0] is False: cat.append("spurious-inconsistency")
        if ks-hs: cat.append("extra-sub")
        if k[2]-hu: cat.append("extra-unsat")
        if hs-ks: cat.append("missing-sub")
        if hu-k[2]: cat.append("missing-unsat")
        cat="+".join(cat) or "ok"
    # does disabling the source TBox fix it?
    if not h["consistent"]: fix = "fixed" if nst[0] is False else "not-fixed"
    else:
        hu=set(h["unsatisfiable"]); hs={tuple(x) for x in h["subsumptions"] if x[0] not in hu and x[1] not in hu}
        ns={x for x in nst[1] if x[0] not in nst[2] and x[1] not in nst[2]}
        fix = "fixed" if (nst[0] and ns==hs and nst[2]==hu) else "not-fixed"
    cats[(cat,fix)]+=1
    print(s,cat,"no-source-tbox:",fix,flush=True)
print(cats)
