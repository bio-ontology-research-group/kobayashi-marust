import subprocess,sys
B=sys.argv[1]; src=sys.argv[2]; out=sys.argv[3]; G=sys.argv[4]
lines=open(src).read().splitlines()
head=[l for l in lines if l.startswith("Prefix") or l.startswith("Ontology") or l.startswith("Declaration")]
ax=[l for l in lines if l not in head and l.strip()!=")"]
def bad(axs):
    open(out,"w").write("\n".join(head+axs+[")"])+"\n")
    r=subprocess.run([B,"classify","--lines",out],capture_output=True,text=True,env={"KM_THREADS":"1","PATH":"/usr/bin:/bin"},timeout=60)
    g=subprocess.run([G,"classify","--lines",out],capture_output=True,text=True,env={"KM_THREADS":"1","PATH":"/usr/bin:/bin"},timeout=60)
    return r.stdout.startswith("CONSISTENT 1") and g.stdout.startswith("CONSISTENT 0")
assert bad(ax)
changed=True
while changed:
    changed=False
    for i in range(len(ax)):
        t=ax[:i]+ax[i+1:]
        if bad(t): ax=t; changed=True; break
bad(ax); print("\n".join(ax))
