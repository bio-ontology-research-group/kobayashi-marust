import subprocess, sys, os, json
S=sys.argv[1]; src=open(sys.argv[2]).read().split("\n")
head=[l for l in src if l.startswith("Prefix") or l.startswith("Ontology") or l.startswith("Declaration")]
ax=[l for l in src if l and not (l.startswith("Prefix") or l.startswith("Ontology") or l.startswith("Declaration") or l==")")]
def text(a): return "\n".join(head+a+[")"])+"\n"
def hermit(t):
    p=S+"/b2/dd.ofn"; open(p,"w").write(t)
    o=subprocess.run(["timeout","120","java","-cp",".:"+open(S+"/oracle/cp.txt").read().strip(),"Oracle",p],cwd=S+"/oracle",capture_output=True,text=True).stdout
    try: return json.loads(o)
    except: return None
def km(t):
    p=S+"/b2/dd_km.ofn"; open(p,"w").write(t)
    env=dict(os.environ); env["KM_ROUTE"]="certified_nominals"
    o=subprocess.run(["timeout","60",S+"/km.h7","classify","--lines",p],capture_output=True,text=True,env=env).stdout
    cons=None; uns=set()
    for l in o.splitlines():
        if l.startswith("CONSISTENT"): cons=l.endswith("1")
        if l.startswith("UNSAT"): uns.add(l.split("\t")[1].lstrip(":"))
    return cons,uns
def bad(a):
    h=hermit(text(a))
    if not h or not h["consistent"] or "Q1" not in h["unsatisfiable"]: return False
    c,u=km(text(a))
    return c is True and "Q1" not in u
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
