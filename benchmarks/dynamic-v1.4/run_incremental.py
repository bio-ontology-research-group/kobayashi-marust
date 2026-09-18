#!/usr/bin/env python3
"""Resource-controlled history runner. Canonical signatures are validated separately."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
import tree_watchdog as watchdog

FACTORIES = dict(hermit='org.semanticweb.HermiT.ReasonerFactory',
    jfact='uk.ac.manchester.cs.jfact.JFactFactory', openllet='openllet.owlapi.OpenlletReasonerFactory',
    elk='org.semanticweb.elk.owlapi.ElkReasonerFactory',whelk='org.geneontology.whelk.owlapi.WhelkOWLReasonerFactory')
BINARY=Path('/ibex/scratch/hohndor/km/v140-release-final-20260916/km.ibex')
RUNTIMES=Path('/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes')
KONCLUDE=Path('/home/hohndor/bench/reasoners/Konclude-v0.7.0-1138-Linux-x64-GCC-Static-Qt5.12.10/Binaries/Konclude')
EXPECTED='ddc30d2f9013b371b5c4ec19c0623c91ecc1b2dbdc172ded9002fd238903d09a'


def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()


def verify_driver(root):
    """Reject stale or modified Java artifacts before starting a measured run."""
    root=root.resolve()
    receipt=root/'driver-build.sha256'
    expected={}
    for line in receipt.read_text().splitlines():
        digest,name=line.split(maxsplit=1)
        name=name.lstrip('*')
        if len(digest)!=64 or any(c not in '0123456789abcdef' for c in digest):
            raise ValueError('invalid driver build digest')
        path=Path(name)
        if path.is_absolute() or '..' in path.parts or name in expected:
            raise ValueError('invalid or duplicate driver build path: '+name)
        expected[name]=digest
    required={'DynamicBenchmark.java','classes/org/kmbenchmark/DynamicBenchmark.class'}
    if not required.issubset(expected):
        raise ValueError('driver build receipt omits source or entry class')
    classes={str(p.relative_to(root)) for p in (root/'classes').rglob('*.class')}
    recorded_classes={p for p in expected if p.endswith('.class')}
    if classes!=recorded_classes:
        raise ValueError('driver class directory differs from build receipt')
    for name,digest in expected.items():
        if sha(root/name)!=digest:
            raise ValueError('driver artifact changed after build: '+name)
    return {'receipt_sha256':sha(receipt),'artifacts':expected}


def save(p,r):
    temp=p.with_suffix('.tmp');temp.write_text(json.dumps(r,indent=2)+'\n');temp.replace(p)


def measure(root,manifest,reasoner,arm,out,timeout):
    driver=verify_driver(root) if reasoner in FACTORIES else None
    out.mkdir(parents=True,exist_ok=False)
    runtime=BINARY if reasoner=='km' else KONCLUDE if reasoner=='konclude' else RUNTIMES/f'classifier-{reasoner}.jar'
    if reasoner=='km':
        assert sha(BINARY)==EXPECTED
        command=['python3',str(root/'km_incremental.py'),str(BINARY),str(manifest),str(out),arm]
    elif reasoner=='konclude':
        assert arm=='fresh'
        command=['python3',str(root/'konclude_incremental.py'),str(KONCLUDE),str(manifest),str(out)]
    else:
        command=['java','-XX:ActiveProcessorCount=1','-Xmx16g','-Delk.reasoner.number_of_workers=1',
            '-cp',f'{root}/classes:{runtime}','org.kmbenchmark.DynamicBenchmark',arm,FACTORIES[reasoner],str(manifest),str(out)]
    record=dict(reasoner=reasoner,arm=arm,status='running',command=command,driver_build=driver,
        runtime_sha256=sha(runtime),manifest_sha256=sha(manifest),
        source_sha256={p.name:sha(p) for p in (root/'DynamicBenchmark.java',root/'km_incremental.py',root/'canonical_km.py',root/'konclude_incremental.py',Path(__file__),root/'tree_watchdog.py')},
        slurm_job=os.environ.get('SLURM_JOB_ID'),slurm_array_job=os.environ.get('SLURM_ARRAY_JOB_ID'),slurm_array_task=os.environ.get('SLURM_ARRAY_TASK_ID'),host=os.uname().nodename,
        history_timeout_s=timeout,state_timeout_s=240,memcap_mib=20480,
        expected_states=len(manifest.read_text().splitlines()),start_epoch=time.time())
    checkpoint=out/'measurement.json';save(checkpoint,record)
    env={k:v for k,v in os.environ.items() if not k.startswith('KM_')}
    env['DYNAMIC_COMPACT']='1'
    if reasoner=='konclude':env['LD_LIBRARY_PATH']='/home/hohndor/bench/compat'
    if manifest.name=='states.txt':env['DYNAMIC_DIGEST_ONLY']='1'
    watchdog.protect_supervisor()
    with (out/'stdout.log').open('wb') as stdout,(out/'driver.stderr').open('wb') as stderr:
        process=subprocess.Popen(command,stdout=stdout,stderr=stderr,env=env,preexec_fn=watchdog.child_preexec)
        def on_trip(status,peak):
            record.update(status=status,peak_mib=peak/2**20);save(checkpoint,record)
        measured=watchdog.monitor(process,timeout=timeout,memcap_bytes=20480*2**20,
            sample_interval=0.02,on_trip=on_trip)
    record.update(status=measured.status,rc=process.returncode,wall_s=measured.wall_s,peak_mib=measured.peak_bytes/2**20)
    stderr=(out/'driver.stderr').read_text(errors='replace')
    record['completed_states']=len(list(out.glob('*.sig.gz')))+len(list(out.glob('*.sig.sha256')))
    if process.returncode==124 or 'STATE_TIMEOUT' in stderr:record['status']='timeout'
    elif process.returncode!=0 and record['status']=='ok':
        record['status']='unsupported' if 'Unsupported' in stderr or 'not supported' in stderr else 'error'
    if record['status']=='ok' and (not (out/'COMPLETE').exists() or record['completed_states']!=record['expected_states']):
        record['status']='incomplete_output'
    save(checkpoint,record)
    return record


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('case');p.add_argument('reasoner',choices=['km','konclude',*FACTORIES])
    p.add_argument('--pilot',action='store_true');p.add_argument('--repetitions',type=int,default=5)
    a=p.parse_args();a.root=a.root.resolve()
    manifest=a.root/'inputs'/a.case/('pilot-states.txt' if a.pilot else 'states.txt')
    output=a.root/('panel-pilot' if a.pilot else 'measured')/a.case/a.reasoner
    arms=['fresh'] if a.reasoner=='konclude' else ['session','fresh']
    if a.reasoner=='konclude':
        output.mkdir(parents=True,exist_ok=True)
        save(output/'capability.json',dict(session='unsupported',reason='OWLlink runtime exposes no Retract operation',fresh='process_rebuild'))
    if not a.pilot:
        for arm in arms:
            measure(a.root,manifest,a.reasoner,arm,output/'warmup'/arm,7200)
    for rep in range(1 if a.pilot else a.repetitions):
        # Reverse paired arm order on alternate repetitions.
        for arm in (arms if rep%2==0 else list(reversed(arms))):
            result=measure(a.root,manifest,a.reasoner,arm,output/f'rep-{rep}'/arm,1800 if a.pilot else 7200)
            print(json.dumps(result),flush=True)
