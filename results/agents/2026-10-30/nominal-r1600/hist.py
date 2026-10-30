import re,collections,sys
lines=[l[6:].strip() for l in open(sys.argv[1]) if l.startswith('DBGCL')]
print(len(lines))
bc=collections.Counter(); hc=collections.Counter(); hyp=collections.Counter(); comp=0
for l in lines:
    b,h=l.split(' -> ')
    atoms=re.findall(r'(Concept \{[^}]*\}|Role \{[^}]*\})',b)
    bc[len(atoms)]+=1
    for a in atoms: hyp[a]+=1
    hc[len(re.findall(r'(P\(|Eq \{|Ineq \{)',h))]+=1
    if re.search(r't: [0-9]{7}|s: [0-9]{7}',l): comp+=1
print('body sizes',sorted(bc.items())); print('head sizes',sorted(hc.items())); print('with composite',comp)
for a,n in hyp.most_common(25): print(n,a)
