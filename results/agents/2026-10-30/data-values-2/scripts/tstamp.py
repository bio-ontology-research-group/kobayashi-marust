import sys,time
t0=time.time()
out=open(sys.argv[1],'w')
for line in sys.stdin:
    out.write(f"{time.time()-t0:9.2f} {line}"); out.flush()
