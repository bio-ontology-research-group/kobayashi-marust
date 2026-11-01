import time
def snap():
    d={}
    for l in open('/proc/stat'):
        if l.startswith('cpu') and l[3].isdigit():
            f=l.split(); v=list(map(int,f[1:])); d[int(f[0][3:])]=(v[3]+v[4], sum(v))
    return d
a=snap(); time.sleep(2); b=snap()
busy={c:1-(b[c][0]-a[c][0])/max(1,(b[c][1]-a[c][1])) for c in a}
print(' '.join(str(c) for c,u in sorted(busy.items()) if u<0.05))
