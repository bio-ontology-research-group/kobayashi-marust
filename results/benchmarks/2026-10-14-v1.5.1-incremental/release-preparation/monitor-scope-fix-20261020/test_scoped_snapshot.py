import pathlib,tempfile,unittest,sys
from unittest.mock import patch
ROOT=pathlib.Path(__file__).parent/'runtime/timing-runner'
sys.path.insert(0,str(ROOT))
import tree_watchdog as w
from scoped_snapshot import ScopedSnapshot
class ScopeTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.root=pathlib.Path(self.tmp.name);self.proc=self.root/'proc';self.cg=self.root/'cgroup';self.proc.mkdir();self.cg.mkdir()
 def tearDown(self):self.tmp.cleanup()
 def process(self,pid,ppid,pgrp,rss=1,cgroup=None):
  d=self.proc/str(pid);d.mkdir();f=['S',str(ppid),str(pgrp)]+['0']*19;f[21]=str(rss);(d/'stat').write_text(f'{pid} (test) '+ ' '.join(f));
  if cgroup is not None:(d/'cgroup').write_text(cgroup)
 def test_nested_detached_worker_and_group_member_counted(self):
  self.process(10,1,10,cgroup='0::/job\n');self.process(11,10,11,rss=3);self.process(12,1,10,rss=5);self.process(90,1,90,rss=100)
  job=self.cg/'job';job.mkdir();(job/'cgroup.procs').write_text('10\n12\n');nested=job/'child';nested.mkdir();(nested/'cgroup.procs').write_text('11\n')
  scope=ScopedSnapshot(10,self.cg)
  with patch.object(w,'snapshot_all',side_effect=AssertionError('unrelated host scan')):snap=scope(str(self.proc))
  self.assertEqual(set(snap),{10,11,12});self.assertEqual(w.tree_and_group_rss(10,10,snap),(9*w.PAGE_SIZE,{10,11,12}))
 def test_v1_memory_scope(self):
  self.process(10,1,10,cgroup='5:cpu,cpuacct:/other\n7:memory:/job\n');job=self.cg/'memory/job';job.mkdir(parents=True);(job/'cgroup.procs').write_text('10\n');scope=ScopedSnapshot(10,self.cg);self.assertEqual(set(scope(str(self.proc))),{10});self.assertEqual(scope.scoped_samples,1)
 def test_missing_or_namespace_mismatched_scope_falls_back(self):
  self.process(10,1,10,cgroup='0::/job\n');self.process(11,10,11);scope=ScopedSnapshot(10,self.cg);self.assertEqual(set(scope(str(self.proc))),{10,11});job=self.cg/'job';job.mkdir();(job/'cgroup.procs').write_text('999999\n');self.assertEqual(set(scope(str(self.proc))),{10,11});self.assertEqual(scope.fallback_samples,2)
 def test_unreadable_nested_scope_falls_back(self):
  self.process(10,1,10,cgroup='0::/job\n');self.process(11,10,11);job=self.cg/'job';job.mkdir();(job/'cgroup.procs').write_text('10\n');(job/'child').mkdir();scope=ScopedSnapshot(10,self.cg);self.assertEqual(set(scope(str(self.proc))),{10,11});self.assertEqual(scope.fallback_samples,1)
 def test_monitor_reuses_scoped_membership_and_enforces_cap(self):
  import subprocess
  child=subprocess.Popen(['sleep','10'],start_new_session=True)
  observed=[];calls=[]
  def scoped(proc='/proc'):
   calls.append(proc)
   return {child.pid:(1,child.pid,100*1024**2)}
  original=w.snapshot_all
  def final_snapshot(proc='/proc'):
   self.assertIsNotNone(child.poll(),'no whole-host scan while the worker is running')
   return original(proc=proc)
  try:
   with patch.object(w,'snapshot_all',side_effect=final_snapshot),patch.object(w,'cgroup_current_bytes',return_value=None):
    result=w.monitor(child,timeout=2,memcap_bytes=32*1024**2,snapshotter=scoped,on_sample=lambda pids:observed.append(set(pids)))
   self.assertEqual(result.status,'memout');self.assertEqual(observed,[{child.pid}]);self.assertEqual(len(calls),1);self.assertLess(child.returncode,0)
  finally:
   if child.poll() is None:child.kill()
   child.wait()
if __name__=='__main__':unittest.main()
