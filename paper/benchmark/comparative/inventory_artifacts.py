"""Verify frozen benchmark artifacts on the compute host; no reasoning runs."""
import argparse, hashlib, json, pathlib, zipfile
parser=argparse.ArgumentParser();parser.add_argument('manifest',type=pathlib.Path);parser.add_argument('output',type=pathlib.Path);args=parser.parse_args()
rows=json.loads(args.manifest.read_text());results=[]
for item in rows:
    row=dict(item);path=pathlib.Path(item['path']) if item.get('path') else None
    if path is None or not path.is_file(): row['status']='artifact_unavailable';results.append(row);continue
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    row['sha256']=h.hexdigest();row['size_bytes']=path.stat().st_size
    row['status']='hash_verified' if item.get('expected_sha256')==row['sha256'] else 'unpinned' if not item.get('expected_sha256') else 'hash_mismatch'
    if item.get('factory'):
        with zipfile.ZipFile(path) as jar:
            row['factory_class_present']=item['factory'].replace('.','/')+'.class' in jar.namelist()
            row['classifier_class_present']='org/kmbenchmark/FullIriClassifier.class' in jar.namelist() or 'org/kmbenchmark/FullIriClassifier3.class' in jar.namelist()
    if item.get('runtime_manifest'):
        manifest=pathlib.Path(item['runtime_manifest']);base=pathlib.Path(item['runtime_root']).resolve()
        runtime=[]
        for line in manifest.read_text().splitlines():
            expected,name=line.split(None,1);file=(base/name.lstrip('*')).resolve();file.relative_to(base)
            digest=hashlib.sha256(file.read_bytes()).hexdigest()
            runtime.append({'path':str(file.relative_to(base)),'sha256':digest,'matches':digest==expected})
        row['runtime_manifest_sha256']=hashlib.sha256(manifest.read_bytes()).hexdigest()
        row['runtime_files']=runtime
        if not all(r['matches'] for r in runtime):row['status']='hash_mismatch'
    results.append(row)
args.output.write_text(json.dumps({'artifacts':results,'scope':'Artifact hashes and packaged classes only; capability and semantic pilots remain required'},indent=2)+'\n')
print(json.dumps({r['id']:r['status'] for r in results}))
assert not any(r['status']=='hash_mismatch' for r in results)
