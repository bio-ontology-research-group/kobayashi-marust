import pathlib,sys,subprocess,resource,time,json,os
root=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(root/'runtime/timing-runner'))
import tree_watchdog as w
from scoped_snapshot import ScopedSnapshot
p=subprocess.Popen(['sleep','3'],start_new_session=True);s=ScopedSnapshot(p.pid);u=resource.getrusage(resource.RUSAGE_SELF);t=time.monotonic();r=w.monitor(p,timeout=5,memcap_bytes=128*1024**2,snapshotter=s);p.wait();v=resource.getrusage(resource.RUSAGE_SELF)
result=dict(status=r.status,sampling=s.summary(),wall=time.monotonic()-t,monitor_cpu=v.ru_utime+v.ru_stime-u.ru_utime-u.ru_stime)
print(json.dumps(result),flush=True)
assert r.status=='ok' and s.scoped_samples>0, 'job cgroup scope unavailable'
(root/('scope-smoke-'+os.environ.get('SLURM_JOB_ID','local')+'.json')).write_text(json.dumps(result,indent=2))
