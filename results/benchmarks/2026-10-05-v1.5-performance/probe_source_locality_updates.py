"""Bounded local retained-vs-fresh diagnostic; never a release benchmark."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import threading
import time

import tree_watchdog as watchdog


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def signature(answer):
    assert answer['dropped'] == 0
    return (answer['consistent'], sorted(answer['subsumptions']), sorted(answer['unsatisfiable']))


def main():
    parser = argparse.ArgumentParser()
    for name in ['binary', 'sources', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=1)
    parser.add_argument('--source-module', action='store_true')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    sources = [args.sources / f'{i:03}.ofn' for i in range(5)]
    requests = [json.dumps({'op': 'init' if i == 0 else 'replace',
                           'functional_syntax': path.read_text()}) + '\n'
                for i, path in enumerate(sources)]
    env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
    env.update(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
               KM_THREADS='1', OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1', KM_TIMING='1')
    cpu = min(os.sched_getaffinity(0))
    receipt = dict(diagnostic_only=True, source_module=args.source_module, binary_sha256=digest(args.binary),
                   sources={path.name: digest(path) for path in sources}, records=[],
                   cpus=1, memory_gib=20, session_timeout_s=180,
                   scope='Five revisions of one ontology; local timings do not establish the full release target.')
    answers = {}

    def save():
        (args.output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

    def prepare():
        watchdog.child_preexec()
        os.sched_setaffinity(0, {cpu})

    save()
    for repetition in range(args.repeats):
        stderr = args.output / f'retained-{repetition}.stderr'
        with stderr.open('w') as error:
            process = subprocess.Popen([str(args.binary.resolve()), 'incremental-source'],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=error, text=True,
                env=dict(env, KM_INCREMENTAL_SOURCE_LOCALITY='1',
                         **({'KM_INCREMENTAL_SOURCE_MODULE':'1'} if args.source_module else {})), preexec_fn=prepare)
            monitored = []
            watcher = threading.Thread(target=lambda: monitored.append(watchdog.monitor(
                process, timeout=180, memcap_bytes=20 * 1024**3)), daemon=True)
            watcher.start()
            try:
                for revision, request in enumerate(requests):
                    started = time.monotonic()
                    process.stdin.write(request)
                    process.stdin.flush()
                    line = process.stdout.readline()
                    elapsed = time.monotonic() - started
                    assert line, 'retained worker exited before answering'
                    response = json.loads(line)
                    assert response['status'] == 'ok', response.get('error')
                    answer = signature(response['result'])
                    answers.setdefault(revision, answer)
                    assert answers[revision] == answer, (repetition, revision)
                    receipt['records'].append(dict(mode='retained', repetition=repetition,
                        revision=revision, wall_s=elapsed, receipt=response.get('receipt')))
                    (args.output / f'retained-{repetition}-{revision}.json').write_text(line)
                    save()
                process.stdin.close()
                assert process.wait(timeout=10) == 0
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                watcher.join(timeout=10)
            assert monitored and monitored[0].status == 'ok'

        for revision, source in enumerate(sources):
            raw = args.output / f'fresh-{repetition}-{revision}.json'
            with raw.open('w') as out, (raw.with_suffix('.stderr')).open('w') as error:
                process = subprocess.Popen([str(args.binary.resolve()), 'classify', str(source)],
                    stdout=out, stderr=error, env=env, preexec_fn=prepare)
                result = watchdog.monitor(process, timeout=180, memcap_bytes=20 * 1024**3)
            assert result.status == 'ok' and process.returncode == 0
            assert signature(json.loads(raw.read_text())) == answers[revision], (repetition, revision)
            receipt['records'].append(dict(mode='fresh', repetition=repetition,
                revision=revision, wall_s=result.wall_s, same_answer=True))
            save()
    print(json.dumps({'completed': True, 'records': len(receipt['records']), 'same_answers': True}))


if __name__ == '__main__':
    main()
