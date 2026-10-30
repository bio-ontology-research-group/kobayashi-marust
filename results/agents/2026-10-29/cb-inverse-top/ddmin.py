# usage: ddmin.py seed.ofn out.ofn  -- greedy one-axiom removal; keeps HermiT 'D unsat' and auto-route miss
import subprocess,json,sys,os,re
S=os.path.dirname(os.path.abspath(__file__)); A=sys.argv[3]; K=sys.argv[4]
src=open(sys.argv[1]).read().splitlines()
head=src[:4]; axioms=[l for l in src[4:] if l.strip() and l.strip()!=')']
def write(ax,p): open(p,'w').write("\n".join(head+ax+[')'])+"\n")
cp=open(A+"/oracle/cp.txt").read().strip()
def bad(ax):
    p=S+"/min/dd_tmp.ofn"; write(ax,p)
    h=subprocess.run(["timeout","60","java","-cp",".:"+cp,"Oracle",p],cwd=A+"/oracle",capture_output=True,text=True).stdout
    try: d=json.loads(h)
    except Exception: return False
    if "D" not in d["unsatisfiable"]: return False
    r=subprocess.run(["timeout","60",K,"classify","--lines",p],capture_output=True,text=True).stdout
    return "UNSAT\t:D" not in r and "CONSISTENT 1" in r
assert bad(axioms)
i=0
while i<len(axioms):
    t=axioms[:i]+axioms[i+1:]
    if bad(t): axioms=t
    else: i+=1
write(axioms,sys.argv[2]); print("\n".join(axioms))
