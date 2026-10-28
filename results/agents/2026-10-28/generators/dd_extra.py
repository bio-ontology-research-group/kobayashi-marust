import subprocess,json,os,sys
S=sys.argv[1]; src=open(sys.argv[2]).read().split("\n")
hd=[l for l in src if l.startswith(("Prefix","Ontology","Declaration"))]
ax=[l for l in src if l and not l.startswith(("Prefix","Ontology","Declaration")) and l!=")"]
def text(a): return "\n".join(hd+a+[")"])+"\n"
def hermit(t):
    p=S+"/sq/dd.ofn"; open(p,"w").write(t)
    o=subprocess.run(["timeout","120","java","-cp",".:"+open(S+"/oracle/cp.txt").read().strip(),"Oracle",p],cwd=S+"/oracle",capture_output=True,text=True).stdout
    try: d=json.loads(o)
    except: return None
    return d["consistent"], set(map(tuple,d["subsumptions"])), set(d["unsatisfiable"])
def km(t):
    p=S+"/sq/dd_km.ofn"; open(p,"w").write(t)
    env={k:v for k,v in os.environ.items() if not k.startswith("KM_")}
    o=subprocess.run(["timeout","60",S+"/km.h7","classify","--lines",p],capture_output=True,text=True,env=env).stdout
    subs=set(); uns=set(); cons=None
    for l in o.splitlines():
        t=l.split("\t")
        if t[0].startswith("CONSISTENT"): cons=t[0].endswith("1")
        elif t[0]=="SUB": subs.add((t[1].lstrip(":"),t[2].lstrip(":")))
        elif t[0]=="UNSAT": uns.add(t[1].lstrip(":"))
    return cons,subs,uns
def bad(a):
    h=hermit(text(a))
    if not h or not h[0]: return False
    k=km(text(a))
    if k[0] is not True: return False
    extra={s for s in k[1] if s not in h[1] and s[0] not in h[2] and s[0]!=s[1]}
    return bool(extra)
assert bad(ax)
n=2
while len(ax)>=2:
    chunk=max(1,len(ax)//n); done=False
    for i in range(0,len(ax),chunk):
        cand=ax[:i]+ax[i+chunk:]
        if bad(cand): ax=cand; n=max(n-1,2); done=True; break
    if not done:
        if n>=len(ax): break
        n=min(len(ax),n*2)
print(text(ax))
