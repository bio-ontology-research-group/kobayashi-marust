"""Prepare one frozen source update stream under a bounded subprocess."""
import hashlib,json,pathlib,subprocess,sys,time
root=pathlib.Path(sys.argv[1]);index=int(sys.argv[2]);job=sys.argv[3]
selection=json.loads((root/'workload-selection.json').read_text())['selected'];row=selection[index]
art=next(r for r in json.loads((root/'artifact-inventory-53198415.json').read_text())['artifacts'] if r['id']=='hermit')
def digest(path):
 h=hashlib.sha256()
 with pathlib.Path(path).open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
assert digest(row['path'])==row['sha256'];assert digest(art['path'])==art['sha256']
out=root/('prepared-updates-'+job)/row['ontology'];out.mkdir(parents=True,exist_ok=False);classes=out/'classes';classes.mkdir()
source=pathlib.Path(__file__).parent/'PrepareUpdates.java';verifier=source.with_name('VerifyUpdates.java');compile_cmd=['javac','--release','11','-cp',art['path'],'-d',str(classes),str(source),str(verifier)]
cmd=['/usr/bin/time','-f','%M','-o',str(out/'max-rss-kib.txt'),'java','-Xmx16g','-XX:ActiveProcessorCount=1','-cp',str(classes)+':'+art['path'],'org.kmbenchmark.PrepareUpdates',row['path'],str(out/'revisions')]
receipt={'ontology':row['ontology'],'source_sha256':row['sha256'],'runtime_sha256':art['sha256'],'generator_sha256':digest(source),'verifier_sha256':digest(verifier),'command':cmd,'compile_command':compile_cmd}
started=time.monotonic()
try:
 with (out/'compile.stdout').open('wb') as stdout,(out/'compile.stderr').open('wb') as stderr:
  subprocess.run(compile_cmd,stdout=stdout,stderr=stderr,check=True,timeout=60)
 with (out/'stdout').open('wb') as stdout,(out/'stderr').open('wb') as stderr:
  result=subprocess.run(cmd,stdout=stdout,stderr=stderr,timeout=900)
 receipt['rc']=result.returncode;receipt['status']='prepared' if result.returncode==0 and (out/'revisions/COMPLETE').exists() else 'preparation_error'
 if receipt['status']=='prepared':
  files={p.name:digest(p) for p in (out/'revisions').iterdir() if p.is_file()};receipt['files']=files
  assert files['000.ofn']==files['002.ofn']==files['004.ofn'],'restoration bytes changed'
except subprocess.TimeoutExpired:receipt['status']='preparation_timeout'
except Exception as e:receipt['status']='preparation_error';receipt['error']=str(e)
receipt['seconds']=time.monotonic()-started
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
