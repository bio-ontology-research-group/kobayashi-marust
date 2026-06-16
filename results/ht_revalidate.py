import sys, os, json, gzip, subprocess, re
HP="/ibex/scratch/hohndor/km-htport"; KM="/ibex/scratch/hohndor/km"
TAB=f"{HP}/engine/target/release/tableau_cli"
def norm(n):
    n=n.strip().lstrip("<").rstrip(">")
    if "#" in n: n=n.rsplit("#",1)[1]
    elif "/" in n: n=n.rsplit("/",1)[1]
    return n.split("__")[0]
def istop(n): return n.lower() in ("thing","owl:thing")
def isbot(n): return n.lower() in ("nothing","owl:nothing")
def clean(pairs):
    out=set()
    for a,b in pairs:
        a,b=norm(a),norm(b)
        if a==b or istop(b) or isbot(a): continue
        out.add((a,b))
    return out
def gold(o):
    p=f"{KM}/gold/konclude__ore_ont_{o}.owl.sig.gz"; s=[]
    for i,ln in enumerate(gzip.open(p,'rt')):
        ln=ln.rstrip('\n')
        if i==0 and ln.strip() in('0','1'): continue
        if '\t' in ln: a,b=ln.split('\t',1); s.append((a,b))
    return clean(s)
onts=sys.argv[1:]
for o in onts:
    tin=f"{HP}/tinD_{o}.json"
    if not os.path.exists(tin):
        em=subprocess.run(["python3",f"{HP}/emit2.py",f"{KM}/corpus/ore_ont_{o}.owl"],
                          capture_output=True,text=True)
        open(tin,"w").write(em.stdout)
    try:
        p=subprocess.run([TAB],stdin=open(tin),capture_output=True,text=True,timeout=200,
                         env=dict(os.environ,KM_HT="1"))
        out=json.loads(p.stdout)
    except Exception as e:
        print(f"{o}: RUNFAIL {str(e)[:40]}"); continue
    k=clean(out.get("subsumptions",[])); g=gold(o)
    us=len(k-g); inc=len(g-k)
    print(f"{o}: unsound={us} incomplete={inc} {'CLEAN' if us==0 and inc==0 else ('UNSOUND' if us else 'INCOMPLETE')}")
