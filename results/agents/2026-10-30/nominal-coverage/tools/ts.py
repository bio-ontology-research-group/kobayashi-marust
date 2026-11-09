import sys,time
t0=time.time()
for line in sys.stdin:
    sys.stdout.write(f"{time.time()-t0:8.2f} {line}"); sys.stdout.flush()
