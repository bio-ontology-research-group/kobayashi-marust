# ddmin.py KM IN OUT : minimise axiom lines while ht_general is wrong vs cb_plain1
import sys,subprocess,os,tempfile
km,inp,outp=sys.argv[1:4]
lines=open(inp).read().splitlines()
hdr=[l for l in lines if l.startswith("Prefix") or l.startswith("Ontology")]
ax=[l for l in lines if l not in hdr and l.strip()!=")"]
D=os.path.dirname(outp)
def run(route,text):
    p=os.path.join(D,"cand_%d.ofn"%os.getpid())
    open(p,"w").write(text)
    env={k:v for k,v in os.environ.items() if not k.startswith("KM_")}; env["KM_ROUTE"]=route
    r=subprocess.run(["timeout","60",km,"classify","--lines",p],capture_output=True,text=True,env=env)
    cons=None;subs=set();uns=set()
    for l in r.stdout.splitlines():
        t=l.split("\t")
        if t[0].startswith("CONSISTENT"): cons=t[0].endswith("1")
        elif t[0]=="SUB": subs.add((t[1],t[2]))
        elif t[0]=="UNSAT": uns.add(t[1])
    if cons is None: return None
    return cons,frozenset(subs),frozenset(uns)
def text(a): return "\n".join(hdr+a+[")"])+"\n"
def bad(a):
    t=text(a); g=run("cb_plain1",t)
    if g is None: return False
    h=run("ht_general",t)
    if h is None: return False
    if not g[0]: return h[0]   # missed inconsistency
    if not h[0]: return False
    # missed subsumption / unsat (not extra)
    return bool(g[1]-h[1]) or bool(g[2]-h[2])
assert bad(ax), "not failing"
n=2
while len(ax)>=2:
    chunk=max(1,len(ax)//n); done=False
    for i in range(0,len(ax),chunk):
        comp=ax[:i]+ax[i+chunk:]
        if comp and bad(comp):
            ax=comp; n=max(n-1,2); done=True; break
    if not done:
        if chunk==1: break
        n=min(len(ax),n*2)
open(outp,"w").write(text(ax))
print(text(ax))
