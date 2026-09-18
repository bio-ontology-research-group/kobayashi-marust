#!/usr/bin/env python3
"""Experimental candidate validation; does not certify or release the candidate."""
import gzip
import importlib.util
import json
from pathlib import Path
import re
from audit_incremental import inspect_arm,sha

ROOT=Path.cwd()
BUILD=ROOT.parent/'abox-candidate-v1'
BASELINE=ROOT.parent/'incremental-driver-v3'
SOURCE_SHA='9a77671d75ed4d72e5cf4786610da1daeedb4054058e9b7c13177d10e691204d'
receipt=dict(line.split('\t',1) for line in (BUILD/'build-receipt.tsv').read_text().splitlines())
assert receipt['Z']=='complete'
assert receipt['source_archive_sha256']==SOURCE_SHA==sha(BUILD/'source.tgz')
binary=BUILD/'km.ibex'
assert receipt['binary_sha256']==sha(binary)
original=(ROOT/'run_incremental.py').read_text()
pinned=re.sub(r'^BINARY=Path\(.*\)$','BINARY=Path('+repr(str(binary))+')',original,flags=re.M)
pinned=re.sub(r"^EXPECTED='[0-9a-f]+'$",'EXPECTED='+repr(receipt['binary_sha256']),pinned,flags=re.M)
assert pinned!=original
pinned_path=ROOT/'candidate_run_incremental.py'
assert not pinned_path.exists()
pinned_path.write_text(pinned)
spec=importlib.util.spec_from_file_location('candidate_runner',pinned_path)
runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
controls=json.loads((ROOT/'inputs/controls.json').read_text())
report={'candidate_build':receipt,'build_receipt_sha256':sha(BUILD/'build-receipt.tsv'),
 'validation_sha256':sha(Path(__file__)),'original_runner_sha256':sha(ROOT/'run_incremental.py'),
 'pinned_runner_sha256':sha(pinned_path),'scope':'experimental controls before Lean certification','cases':{},'pass':True}
for case,analytic in controls.items():
 manifest=ROOT/'inputs'/case/'pilot-states.txt'
 expected=len(manifest.read_text().splitlines())
 checks={}
 refs={}
 for reasoner in ('hermit','jfact'):
  directory=BASELINE/'panel-pilot'/case/reasoner/'rep-0/fresh'
  check=inspect_arm(directory,manifest,expected,reasoner,'fresh',analytic)
  assert check['complete'],(case,reasoner,check['issues'])
  refs[reasoner]=directory
 for i in range(expected):
  with gzip.open(refs['hermit']/f'{i:03d}.sig.gz','rb') as f:h=f.read()
  with gzip.open(refs['jfact']/f'{i:03d}.sig.gz','rb') as f:j=f.read()
  assert h==j,(case,i,'independent references disagree')
 for arm in ('session','fresh'):
  out=ROOT/'panel-pilot'/case/'km'/'rep-0'/arm
  measurement=runner.measure(ROOT,manifest,'km',arm,out,1800)
  inspected=inspect_arm(out,manifest,expected,'km',arm,analytic)
  mismatches=[]
  for i in range(expected):
   path=out/f'{i:03d}.sig.gz'
   if not path.exists():mismatches.append(i);continue
   with gzip.open(path,'rb') as f:actual=f.read()
   with gzip.open(refs['hermit']/f'{i:03d}.sig.gz','rb') as f:reference=f.read()
   if actual!=reference:mismatches.append(i)
  ok=inspected['complete'] and not mismatches
  checks[arm]={'pass':ok,'mismatch_revisions':mismatches,'inspection':inspected,
    'reference_measurement_sha256':{r:sha(d/'measurement.json') for r,d in refs.items()}}
  report['pass']=report['pass'] and ok
 report['cases'][case]=checks
 (ROOT/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
assert report['pass'],'candidate control validation failed: inspect validation.json'
(ROOT/'PASS').write_text(json.dumps({'candidate_sha256':receipt['binary_sha256'],'validation_sha256':sha(ROOT/'validation.json'),'scope':'six analytic histories; both arms; independent exact full taxonomy'})+'\n')
