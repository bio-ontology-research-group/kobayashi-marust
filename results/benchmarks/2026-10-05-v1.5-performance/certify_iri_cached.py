import os,json,hashlib,subprocess
from pathlib import Path
root=Path('results/benchmarks/2026-10-05-v1.5-performance')
manifest=root/'iri-classification-source-manifest.json'
files=json.loads(manifest.read_text())['files']
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check():
 assert all(digest(p)==v for p,v in files.items()), 'Pinned source changed'
receipt={'source_manifest_sha256':digest(manifest),'gates':[],'release_approved':False}
env=dict(os.environ,PATH='/state/elan/bin:/state/cargo/bin:'+os.environ['PATH'],ELAN_HOME='/state/elan',CARGO_HOME='/state/cargo',RUSTUP_HOME='/state/rustup',KM_WORK_ROOT=str(Path('.work/atmost-certification').resolve()),KM_CERT_KEEP_NATIVE_CHECKERS='1',KM_FAST_IRI_GRAMMAR='1',CARGO_PROFILE_RELEASE_LTO='false',CARGO_PROFILE_RELEASE_CODEGEN_UNITS='16')
for gate in ['ht','routing','elc','cb']:
 check()
 log=Path('/tmp/agent/km-v150-diagnostics')/('iri-cached-'+gate+'-gate.log')
 with log.open('w') as out:
  code=subprocess.run(['bash','lean/run-'+gate+'-certification-gate.sh'],env=env,stdout=out,stderr=subprocess.STDOUT).returncode
 check()
 surface=Path('.work/atmost-certification/artifacts')/(gate+'-certification-surface.log')
 row={'gate':gate,'exit_code':code,'log_sha256':digest(log),'surface_sha256':digest(surface),'sorryAx':'sorryAx' in surface.read_text()}
 receipt['gates'].append(row);receipt['source_files_rechecked']=len(files)
 (root/'iri-cached-certification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 assert code==0 and not row['sorryAx'], row
 print(json.dumps(row),flush=True)
