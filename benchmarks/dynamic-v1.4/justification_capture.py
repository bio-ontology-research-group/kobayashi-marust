#!/usr/bin/env python3
"""Capture observed native oracle source versions without changing KM's binary."""
import argparse,hashlib,json,os,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('binary');p.add_argument('input',type=Path);p.add_argument('sub');p.add_argument('super');p.add_argument('out',type=Path);a=p.parse_args()
a.out.mkdir(parents=True,exist_ok=True);tmp=a.out/'tmp';tmp.mkdir(exist_ok=True)
env={k:v for k,v in os.environ.items() if not k.startswith('KM_')};env.update(KM_THREADS='1',KM_ROUTE_TRACE='1',TMPDIR=str(tmp.resolve()))
start=time.monotonic();seen=set();rows=[]
with (a.out/'stdout').open('w') as stdout,(a.out/'stderr').open('w') as stderr:
 proc=subprocess.Popen(['timeout','-k','5','600',a.binary,'explain','--max-axioms','1000000','--max-checks','10000000',str(a.input),'subclass',a.sub,a.super],stdout=stdout,stderr=stderr,env=env)
 while proc.poll() is None:
  for f in tmp.glob('*.explain.ofn'):
   try:data=f.read_bytes()
   except FileNotFoundError:continue
   digest=hashlib.sha256(data).hexdigest()
   if digest not in seen:
    # Polling can miss quick intermediate calls; these are observed states,
    # never claimed to be a complete call trace or exact call index.
    seen.add(digest);dest=a.out/('observed-%04d.ofn'%len(rows));dest.write_bytes(data)
    rows.append({'file':dest.name,'sha256':digest,'observed_s':time.monotonic()-start})
    (a.out/'observations.json').write_text(json.dumps(rows,indent=2)+'\n')
  time.sleep(.025)
 (a.out/'exit-code').write_text(str(proc.returncode)+'\n')
if rows:
 last=a.out/rows[-1]['file']
 with (a.out/'replay.stdout').open('w') as stdout,(a.out/'replay.stderr').open('w') as stderr:
  replay=subprocess.run(['timeout','-k','5','240',a.binary,'classify',str(last)],stdout=stdout,stderr=stderr,env=env)
 (a.out/'replay.exit-code').write_text(str(replay.returncode)+'\n')
