#!/usr/bin/env python3
"""One-shot source JSON oracle, matching KM's init response for the common extractor.

Set KONCLUDE_BIN and LD_LIBRARY_PATH for the deployment. This performs a fresh
OWLlink classification for every oracle call; it claims no retained reasoning.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from konclude_incremental import canonical, request


def main():
    binary = os.environ.get('KONCLUDE_BIN', '/ibex/scratch/hohndor/km/Konclude-official')
    root = Path(os.environ.get('TMPDIR', '.work/inputs'))
    root.mkdir(parents=True, exist_ok=True)
    payload = json.loads(sys.stdin.readline())
    if payload.get('op') != 'init' or not isinstance(payload.get('functional_syntax'), str):
        raise ValueError('only an init source request is supported')
    with tempfile.TemporaryDirectory(prefix='konclude-oracle-', dir=root) as tmp:
        tmp = Path(tmp)
        source, req, response = tmp / 'source.ofn', tmp / 'request.xml', tmp / 'response.xml'
        source.write_text(payload['functional_syntax'])
        request(source, req)
        with (tmp / 'stdout').open('w') as stdout, (tmp / 'stderr').open('w') as stderr:
            proc = subprocess.Popen([binary, 'owllinkfile', '-w', '1', '-i', str(req), '-o', str(response)],
                                    stdout=stdout, stderr=stderr)
            try:
                rc = proc.wait(timeout=float(os.environ.get('KONCLUDE_TIMEOUT', '240')))
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
                raise RuntimeError('Konclude oracle timeout')
        if rc:
            raise RuntimeError(f'Konclude exit {rc}: {(tmp / "stderr").read_text()[-2000:]}')
        # OWLlink can return success for later queries after input processing
        # errors. Reject an error-bearing log rather than classifying a subset.
        log = (tmp / 'stdout').read_text() + (tmp / 'stderr').read_text()
        if any(word in log.lower() for word in ('parsing error', 'parse error', 'unsupported', 'not supported')):
            raise RuntimeError('Konclude reported unsupported input or a parse error')
        rows = [line.split('\t') for line in canonical(response)]
        result = dict(consistent=['C', 'true'] in rows, dropped=[],
                      unsatisfiable=[r[1] for r in rows if r[0] == 'U'],
                      subsumptions=[r[1:] for r in rows if r[0] == 'S'])
        print(json.dumps(dict(status='ok', result=result)), flush=True)

if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print(json.dumps(dict(status='error', error=str(exc))), flush=True)
        sys.exit(1)
