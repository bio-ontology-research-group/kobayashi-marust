#!/usr/bin/env python3
"""Measure KM or Konclude and fingerprint its full-IRI taxonomy."""

from __future__ import annotations

import argparse, functools, hashlib, json, os
from pathlib import Path
import subprocess, sys, time
import tree_watchdog as watchdog


def sha256(path: Path) -> str:
    value=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(8*1024*1024),b''): value.update(block)
    return value.hexdigest()


def publish(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True,exist_ok=True)
    temporary=Path(str(path)+f'.part.{os.getpid()}')
    temporary.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    temporary.replace(path)


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--baseline',choices=('km','konclude'),required=True)
    parser.add_argument('--binary',type=Path,required=True)
    parser.add_argument('--library-path',type=Path)
    parser.add_argument('--ontology',type=Path,required=True)
    parser.add_argument('--input-ontology',type=Path,
                        help='semantics-preserving serialization supplied to the runtime')
    parser.add_argument('--ontology-id',required=True)
    parser.add_argument('--output-root',type=Path,required=True)
    parser.add_argument('--tools-root',type=Path,required=True)
    parser.add_argument('--timeout',type=float,default=600)
    parser.add_argument('--memcap-mb',type=int,default=32768)
    args=parser.parse_args()
    runtime_ontology=args.input_ontology or args.ontology
    for path in (args.binary,args.ontology,runtime_ontology):
        if not path.is_file() or path.stat().st_size==0: raise SystemExit(f'missing artifact: {path}')
    if args.baseline=='konclude' and (args.library_path is None or not args.library_path.is_dir()):
        raise SystemExit('Konclude runtime library directory missing')

    prefix=args.output_root/args.baseline/args.ontology_id
    result_path=Path(str(prefix)+'.result.json')
    suffix='.json' if args.baseline=='km' else '.owlxml'
    output_path=Path(str(prefix)+'.taxonomy'+suffix)
    output_temporary=Path(str(output_path)+'.part')
    stderr_path=Path(str(prefix)+'.stderr')
    time_path=Path(str(prefix)+'.time')
    prefix.parent.mkdir(parents=True,exist_ok=True)
    for path in (output_path,output_temporary,stderr_path,time_path):
        try:path.unlink()
        except FileNotFoundError:pass

    environment=dict(os.environ)
    if args.baseline=='km':
        environment.update(KM_ROUTE='auto',KM_THREADS='16')
        command=[str(args.binary),'classify',str(runtime_ontology)]
        output_format='json'
    else:
        environment['LD_LIBRARY_PATH']=str(args.library_path)+':'+environment.get('LD_LIBRARY_PATH','')
        command=[str(args.binary),'classification','-w','16','-v','-i',str(runtime_ontology),'-o',str(output_temporary)]
        output_format='owlxml'
    measured_command=['/usr/bin/time','-v','-o',str(time_path)]+command
    record={'schema':1,'baseline':args.baseline,'ontology_id':args.ontology_id,
            'ontology':str(args.ontology),'ontology_sha256':sha256(args.ontology),
            'input_ontology':str(runtime_ontology),'input_ontology_sha256':sha256(runtime_ontology),
            'binary':str(args.binary),'binary_sha256':sha256(args.binary),'command':command,
            'measured_command':measured_command,
            'explicit_environment':{'KM_ROUTE':'auto','KM_THREADS':'16'} if args.baseline=='km' else {},
            'timeout_s':args.timeout,'memory_limit_mb':args.memcap_mb,'status':'running',
            'host':os.uname().nodename,'slurm_job_id':os.getenv('SLURM_JOB_ID'),
            'slurm_array_job_id':os.getenv('SLURM_ARRAY_JOB_ID'),
            'slurm_array_task_id':os.getenv('SLURM_ARRAY_TASK_ID'),'runner_sha256':sha256(Path(__file__))}
    publish(result_path,record)
    started=time.monotonic(); watchdog.protect_supervisor()
    stderr=stderr_path.open('wb')
    stdout=output_temporary.open('wb') if args.baseline=='km' else subprocess.DEVNULL
    process=subprocess.Popen(measured_command,env=environment,stdin=subprocess.DEVNULL,stdout=stdout,stderr=stderr,
                             preexec_fn=watchdog.child_preexec)
    def on_trip(status,peak):
        checkpoint=dict(record);checkpoint.update(status=status,wall_s=round(time.monotonic()-started,4),
            peak_mb=round(peak/2**20,2),checkpointed=True);publish(result_path,checkpoint)
    measured=watchdog.monitor(process,timeout=args.timeout,memcap_bytes=args.memcap_mb*2**20,
                              sample_interval=.02,on_trip=on_trip)
    if args.baseline=='km':stdout.close()
    stderr.close()
    direct_peak=0
    if time_path.is_file():
        for line in time_path.read_text(encoding='utf-8',errors='replace').splitlines():
            if 'Maximum resident set size' in line:
                direct_peak=int(line.rsplit(':',1)[1].strip())*1024;break
    peak=max(measured.peak_bytes,direct_peak)
    record.update(status=measured.status,rc=process.returncode,wall_s=round(measured.wall_s,4),
                  peak_mb=round(peak/2**20,2),stderr_sha256=sha256(stderr_path),checkpointed=True)
    if record['status']=='ok' and process.returncode!=0:record['status']='error'
    if record['status']=='ok':
        if not output_temporary.is_file() or output_temporary.stat().st_size==0:record['status']='output_error'
        else:
            output_temporary.replace(output_path)
            fingerprint=subprocess.run([sys.executable,str(args.tools_root/'full_iri_fingerprint.py'),
                '--input',str(output_path),'--format',output_format,'--source-ontology',str(args.ontology),
                '--output-prefix',str(prefix)+'.fingerprint'],text=True,capture_output=True)
            if fingerprint.returncode!=0:record.update(status='fingerprint_error',fingerprint_error=fingerprint.stderr[-1000:])
            else:
                fp=json.loads(fingerprint.stdout)
                if args.baseline=='konclude' and fp.get('missing_source_declarations')!=0:
                    record.update(status='output_error',output_error='taxonomy omits source class declarations',
                                  missing_source_declarations=fp.get('missing_source_declarations'))
                record.update(output_sha256=sha256(output_path),
                    consistency=str(fp['consistent']).lower(),subsumptions=fp['subsumptions'],
                    unsatisfiable=fp['unsatisfiable'],taxonomy_sha256=fp['taxonomy_sha256'],
                    relation_sha256=fp['relation_sha256'],
                    fingerprint_wall_s=fp['wall_s'],fingerprint_peak_mb=fp['peak_mb'])
    publish(result_path,record);print(json.dumps(record,sort_keys=True),flush=True)


if __name__=='__main__':main()
