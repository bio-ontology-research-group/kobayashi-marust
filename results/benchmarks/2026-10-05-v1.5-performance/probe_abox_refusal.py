import os,sys,json,subprocess,hashlib,shutil
from pathlib import Path
p=Path.cwd()/'results/benchmarks/2026-10-05-v1.5-performance';sys.path.insert(0,str(p))
import tree_watchdog as w
w.protect_supervisor()
t=Path('/tmp/agent/km-v150-diagnostics');binary=Path('.work/target-diagnostic/release/km').resolve()
def digest(f):return hashlib.sha256(f.read_bytes()).hexdigest()
pinned=t/('km-abox-diagnostic-'+digest(binary)[:12]);shutil.copy2(binary,pinned)
flags=json.loads((p/'production-v150-full-artifact.json').read_text())['flags'];env={k:v for k,v in os.environ.items() if not k.startswith('KM_')};env.update(flags,KM_TIMING='1',KM_THREADS='1',KM_ROUTE='auto',RAYON_NUM_THREADS='1',OMP_NUM_THREADS='1')
r={'diagnostic_only':True,'binary_sha256':digest(pinned),'source_commit':'ef84dcf1 plus optional ABox refusal diagnostic','source_change_sha256':digest(Path('engine/src/orchestrate/cb_to_ht.rs')),'attempts':[],'release_approved':False}
cpu=min(os.sched_getaffinity(0))
def preexec():w.child_preexec();os.sched_setaffinity(0,{cpu})
for name in ['1342','14379']:
 source=t/'timeout-profile-sources'/('ore_ont_'+name+'.owl');out=t/('abox-refusal-'+name);out.mkdir(exist_ok=False)
 with (out/'stdout').open('w') as stdout,(out/'stderr').open('w') as stderr:
  proc=subprocess.Popen([str(pinned),'classify',str(source)],env=env,stdout=stdout,stderr=stderr,preexec_fn=preexec)
  e=w.monitor(proc,timeout=5,memcap_bytes=20*1024**3)
 lines=(out/'stderr').read_text().splitlines();row={'ontology':'ore_ont_'+name,'source_sha256':digest(source),'status':e.status,'exit_code':proc.returncode,'wall_s':e.wall_s,'stderr_sha256':digest(out/'stderr'),'trace':lines};r['attempts'].append(row)
 (p/'abox-refusal-diagnostic.json').write_text(json.dumps(r,indent=2)+'\n');print(name,e.status,lines[:18],flush=True)
