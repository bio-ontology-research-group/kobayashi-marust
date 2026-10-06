"""Bounded route diagnosis for the largest measured shared-runtime gap."""
import os,json,subprocess,hashlib,sys
from pathlib import Path
import tree_watchdog as watchdog
root=Path(__file__).resolve().parent
source=Path('/tmp/agent/km-v150-diagnostics/mean-tail-sources/ore_ont_4410.owl')
binary=Path('/workspace/.work/target-integral-decimal/release/km')
work=Path('/tmp/agent/km-v150-diagnostics/mean-tail-4410-ground-v1');work.mkdir(exist_ok=False)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
row=next(r for r in json.loads((root/'full-candidate-inputs.json').read_text())['inputs'] if r['ontology']=='ore_ont_4410')
assert digest(source)==row['sha256']
flags=dict(KM_HT_NATIVE_FULL='1',KM_GROUND_RULE_SOURCE='1',KM_HT_DDB='1',KM_CACHE_CONFORMANCE='1',KM_FAST_IRI_GRAMMAR='1',KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1',KM_TIMING='1',KM_BRIDGE_PROGRESS='1',KM_HT_STATS='1',KM_CONFORMANCE_TIMING='1',KM_THREADS='1',RAYON_NUM_THREADS='1',OMP_NUM_THREADS='1')
env={k:v for k,v in os.environ.items() if not k.startswith('KM_')};env.update(flags)
watchdog.protect_supervisor();cpu=min(os.sched_getaffinity(0))
def child():
 watchdog.child_preexec();os.sched_setaffinity(0,{cpu})
report=dict(diagnostic_only=True,release_approved=False,binary_sha256=digest(binary),source_sha256=digest(source),flags=flags,timeout_s=15,memory_gib=20,cpus=1,attempts=[])
for route in ['ht_bridge']:
 out=work/(route+'.json');err=work/(route+'.stderr')
 with out.open('w') as o,err.open('w') as e:
  proc=subprocess.Popen([str(binary),'classify','--route',route,str(source)],env=env,stdout=o,stderr=e,preexec_fn=child)
  watched=watchdog.monitor(proc,timeout=15,memcap_bytes=20*1024**3)
 report['attempts'].append(dict(route=route,status=watched.status,exit_code=proc.returncode,wall_s=watched.wall_s,peak_bytes=watched.peak_bytes,trace=err.read_text().splitlines(),output_sha256=digest(out)))
 print(route,watched.status,proc.returncode,flush=True)
 (root/'mean-tail-4410-ground-v1.json').write_text(json.dumps(report,indent=2)+'\n')
