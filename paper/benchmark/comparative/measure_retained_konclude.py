"""Retained Konclude HTTP session with independent resource limits per revision."""
import http.client
import json
import os
from pathlib import Path
import socket
import subprocess
import threading
import time
import xml.etree.ElementTree as ET
import tree_watchdog as watchdog
from measure_classification import digest
from owllink_requests import axioms, request, hierarchy_request
from owllink_taxonomy import NS, parse


def measure(row, revisions, output, timeout=240, memory_mib=20480):
    output=Path(output).resolve(); output.mkdir(parents=True,exist_ok=False)
    record={'baseline':'konclude','mode':'retained OWLlink HTTP knowledge base',
            'internal_reuse':'not inferred from interface','artifact_sha256':row['sha256'],
            'runner_sha256':digest(__file__),'revisions':[],'status':'preparing',
            'timeout_per_revision_s':timeout,'memory_mib':memory_mib}
    def publish():
        temporary=output/'record.json.part';temporary.write_text(json.dumps(record,indent=2)+'\n');temporary.replace(output/'record.json')
    publish(); process=None;worker=None
    try:
        assert digest(row['path'])==row['sha256'],'runtime hash mismatch'
        for r in revisions:
            assert digest(r['path'])==r['sha256'],'OWL/XML revision hash mismatch'
        with socket.socket() as reservation:
            reservation.bind(('127.0.0.1',0));port=reservation.getsockname()[1]
        cpu=min(os.sched_getaffinity(0))
        command=[row['path'],'owllinkserver','-w','1','-p',str(port)]
        record.update(command=command,cpu_affinity=[cpu],host=os.uname().nodename)
        def child():
            watchdog.child_preexec();os.sched_setaffinity(0,{cpu})
        watchdog.protect_supervisor()
        with (output/'stdout').open('wb') as stdout,(output/'stderr').open('wb') as stderr:
            process=subprocess.Popen(command,stdout=stdout,stderr=stderr,stdin=subprocess.DEVNULL,
                env=dict(os.environ,LD_LIBRARY_PATH=str(Path(row['path']).parent/'runtime-lib')),preexec_fn=child)
            previous={}
            for index,revision in enumerate(revisions):
                stage=dict(revision,revision=index,status='running');record['revisions'].append(stage);publish()
                completed=threading.Event();received={};started=time.monotonic()
                def exchange():
                    try:
                        current=axioms(revision['path'])
                        payload,removed,added=request(previous,current,initial=index==0)
                        received.update(current=current,removed=removed,added=added)
                        (output/f'{index:03}.request.xml').write_bytes(payload)
                        response_number=0
                        def post(body):
                            nonlocal response_number
                            connection=http.client.HTTPConnection('127.0.0.1',port,timeout=max(.1,timeout-(time.monotonic()-started)))
                            try:
                                connection.request('POST','/',body,{'Content-Type':'application/xml'})
                                response=connection.getresponse();raw=response.read()
                                (output/f'{index:03}.http-{response_number}.xml').write_bytes(raw)
                                response_number+=1
                                if response.status!=200:raise ValueError('HTTP status '+str(response.status))
                                return ET.fromstring(raw)
                            finally:connection.close()
                        # Retry only connection refusal while the newly launched server starts.
                        while True:
                            try: root=post(payload);break
                            except ConnectionRefusedError:
                                if index or process.poll() is not None or time.monotonic()-started>=timeout:raise
                                time.sleep(.02)
                        if root.tag!='{'+NS+'}ResponseMessage':raise ValueError('unexpected response root')
                        allowed={'{'+NS+'}'+n for n in ['KB','OK','BooleanResponse']}
                        if any(e.tag not in allowed for e in root):raise ValueError('failed update response')
                        booleans=root.findall('{'+NS+'}BooleanResponse')
                        if len(booleans)!=1 or booleans[0].get('result') not in ['true','false']:raise ValueError('missing consistency response')
                        if booleans[0].get('result')=='true':
                            hierarchy=post(hierarchy_request())
                            if len(hierarchy)!=1 or hierarchy[0].tag!='{'+NS+'}ClassHierarchy':raise ValueError('failed hierarchy response')
                            root.append(hierarchy[0])
                        raw=ET.tostring(root,encoding='utf-8',xml_declaration=True)
                        (output/f'{index:03}.response.xml').write_bytes(raw)
                        received['taxonomy']=parse(raw,revision['classes'])
                    except Exception as error:received['error']=str(error)
                    finally:completed.set()
                worker=threading.Thread(target=exchange,daemon=True);worker.start()
                result=watchdog.monitor(process,timeout=timeout,memcap_bytes=memory_mib*1024**2,until=completed.is_set)
                stage.update(status=result.status,wall_s=time.monotonic()-started,peak_bytes=result.peak_bytes)
                if result.status!='ready':
                    record['status']=result.status;publish();break
                worker.join(timeout=1)
                if 'error' in received:raise ValueError(received['error'])
                taxonomy=output/f'{index:03}.taxonomy.json';taxonomy.write_text(json.dumps(received['taxonomy'])+'\n')
                stage.update(status='executed_unvalidated',taxonomy_sha256=digest(taxonomy),removed=received['removed'],added=received['added'])
                previous=received['current'];publish()
            else:record['status']='executed_unvalidated'
    except Exception as error:
        record.update(status='adapter_error',error=str(error))
        if record['revisions'] and record['revisions'][-1]['status'] in ['ready','running']:
            record['revisions'][-1].update(status='adapter_error',error=str(error))
    finally:
        if process is not None and process.poll() is None:
            _,members=watchdog.tree_and_group_rss(process.pid,process.pid,watchdog.snapshot_all());watchdog.kill_tree(members);process.wait()
        if worker is not None:worker.join(timeout=5)
    for index in range(len(record['revisions']),len(revisions)):
        record['revisions'].append(dict(revisions[index],revision=index,status='not_run_after_session_failure'))
    publish();return record
