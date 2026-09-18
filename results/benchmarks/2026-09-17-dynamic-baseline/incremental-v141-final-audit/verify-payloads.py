import hashlib,json,os
from pathlib import Path
root=Path('/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/v141-incremental-final')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
x=json.loads((root/'main-audit.json').read_text()); files={}; runtimes={}
assert sha(root/'incremental-panel.tsv')==x['panel_sha256']
assert sha(root/'deployment.json')==x['deployment_sha256']
source_hashes={}
for case,c in x['cases'].items():
 inp=root/'inputs'/case
 lines=(inp/'SHA256SUMS').read_text().splitlines()
 assert len(lines)==251
 manifest=(inp/'states.txt').read_text().splitlines()
 assert len(manifest)==251
 for line,path in zip(lines,manifest):
  h,name=line.split(None,1);assert Path(name).resolve()==Path(path).resolve()
  assert sha(Path(name))==h,name
  files[name]=h
 for r in c['repetitions'].values():
  for a in r['arms'].values():
   m=a['measurement'];cmd=m['command']
   assert sha(inp/'states.txt')==m['manifest_sha256']==c['manifest_sha256']
   for name,h in m['source_sha256'].items():
    if name not in source_hashes:source_hashes[name]=sha(root/name)
    assert source_hashes[name]==h,name
   runtime=cmd[2] if cmd[0]=='python3' else cmd[cmd.index('-cp')+1].split(':')[-1]
   assert Path(runtime).is_file(),runtime
   if runtime not in runtimes:runtimes[runtime]=sha(Path(runtime))
   assert runtimes[runtime]==m['runtime_sha256'],runtime
out=dict(input_files=len(files),input_hashes=files,runtime_hashes=runtimes,audit_sha256=sha(root/'main-audit.json'),verifier_sha256=sha(Path(__file__)),slurm_job=os.environ.get('SLURM_JOB_ID'),status='pass')
(root/'parent-payload-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(files),'input files;',len(runtimes),'runtimes')
