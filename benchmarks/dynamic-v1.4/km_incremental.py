#!/usr/bin/env python3
"""Measure KM source sessions; external timeout bounds the entire pilot arm."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time


from canonical_km import canonical


def run(binary, manifest, out, arm):
    out.mkdir(parents=True, exist_ok=True)
    env = {k:v for k,v in os.environ.items() if not k.startswith('KM_')}
    env.update(KM_THREADS='1')
    proc = None
    timing = ['revision\trequest_response_s\tcanonicalize_s']
    try:
        with (out / 'stderr.log').open('w') as err:
            for i,path in enumerate(manifest.read_text().splitlines()):
                signal.alarm(240)
                source = gzip.open(path,'rt').read() if path.endswith('.gz') else Path(path).read_text()
                if proc is None:
                    proc = subprocess.Popen([binary,'incremental-source'], stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE, stderr=err, text=True, env=env)
                op = 'init' if arm == 'fresh' or i == 0 else 'replace'
                t = time.perf_counter()
                proc.stdin.write(json.dumps({'op':op,'functional_syntax':source})+'\n')
                proc.stdin.flush()
                reply = proc.stdout.readline()
                elapsed = time.perf_counter()-t
                if not reply: raise RuntimeError(f'worker exited {proc.poll()}')
                value = json.loads(reply)
                if value['status'] != 'ok': raise RuntimeError(value)
                canonical_start = time.perf_counter()
                signature = canonical(value['result'], source)
                canonical_s = time.perf_counter()-canonical_start
                if os.environ.get('DYNAMIC_DIGEST_ONLY') == '1':
                    (out / f'{i:03}.sig.sha256').write_text(hashlib.sha256(signature.encode()).hexdigest()+'\n')
                    value = {k:v for k,v in value.items() if k != 'result'}
                elif os.environ.get('DYNAMIC_COMPACT') == '1':
                    with gzip.open(out / f'{i:03}.sig.gz','wt') as f:
                        f.write(signature)
                    value = {k:v for k,v in value.items() if k != 'result'}
                else:
                    (out / f'{i:03}.sig').write_text(signature)
                (out / f'{i:03}.json').write_text(json.dumps(value,sort_keys=True)+'\n')
                timing.append(f'{i}\t{elapsed}\t{canonical_s}')
                (out / 'timings.tsv').write_text('\n'.join(timing)+'\n')
                signal.alarm(0)
            if proc:
                proc.stdin.close()
                if proc.wait() != 0: raise RuntimeError('worker failed')
                proc = None
        (out / 'timings.tsv').write_text('\n'.join(timing)+'\n')
        (out / 'COMPLETE').write_text(f'states={len(timing)-1}\n')
    finally:
        signal.alarm(0)
        if proc:
            proc.kill()
            proc.wait()


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('binary')
    p.add_argument('manifest',type=Path)
    p.add_argument('out',type=Path)
    p.add_argument('arm',choices=['session','fresh'])
    a = p.parse_args()
    def timeout(signum, frame):
        raise TimeoutError('STATE_TIMEOUT after 240 seconds')
    signal.signal(signal.SIGALRM, timeout)
    run(a.binary,a.manifest,a.out,a.arm)
