#!/usr/bin/env python3
"""Checkers-on suite: run `km classify` with and without the Lean checkers.

usage:
  python3 -I tools/checkers_on_suite.py run --km KM --checkers DIR --out OUT
        [--jobs 4] [--timeout 60] [--modes off,on,ht] [--gold DIR ...]
        INPUTS.tsv ...
  python3 -I tools/checkers_on_suite.py summarize OUT

INPUTS.tsv has one input per line: `family<TAB>path`. Every KM_* variable of
the caller is removed. Each run gets KM_THREADS=1, KM_TIMING=1 (for the route
line) and a private TMPDIR under OUT/tmp. Modes:

  off  no checker
  on   KM_LEAN_CHECKERS=DIR (ELC and CB publication checkers; HT unchecked)
  ht   on + KM_LEAN_CHECKERS_HT=1 (certified HT workers)
  all  on + KM_LEAN_CHECKERS_SET=all (CB component wires too)

Results go to OUT/results.jsonl (one record per input and mode); `summarize`
writes OUT/summary.md and OUT/per-input.tsv. Gold answers (HermiT JSON with
`consistent`, `subsumptions`, `unsatisfiable`, as cached by the differential
tools in results/agents/2026-10-29/*/diff_run.py) are looked up by file stem
in each --gold directory.
"""
import concurrent.futures as cf
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time

PUBLICATION = {
    'elc-publication', 'cb-source-exact-taxonomy', 'cb-source-production-taxonomy',
    'ht-taxonomy', 'ht-global-verdict',
}
EVENT = re.compile(r'^KM_LEAN_CHECK (accepted|rejected|cannot_check) family=(\S+) '
                   r'checker=(\S+) certificate=(\S+) bytes=(\d+) worker_pid=(\d+)(?: detail=(.*))?$')
ROUTE = re.compile(r'frontend done @ [0-9.]+s route=(\S+)')


def strip(name):
    return name.lstrip(':').split('#')[-1].split('>')[0]


def parse_answer(text):
    cons, subs, uns = None, set(), set()
    for line in text.splitlines():
        t = line.split('\t')
        if t[0].startswith('CONSISTENT'):
            cons = t[0].strip().endswith('1')
        elif t[0] == 'SUB' and len(t) == 3:
            subs.add((strip(t[1]), strip(t[2])))
        elif t[0] == 'UNSAT' and len(t) == 2:
            uns.add(strip(t[1]))
    if cons is None:
        return None
    if not cons:
        # Every class is unsatisfiable in an inconsistent ontology; routes
        # differ only in how many UNSAT lines they print.
        return False, set(), set()
    subs = {s for s in subs if s[0] not in uns and s[1] not in uns and s[0] != s[1]}
    return cons, subs, uns


def gold_answer(dirs, path):
    stem = os.path.splitext(os.path.basename(path))[0]
    beside = os.path.splitext(path)[0] + '.hermit.json'
    stems = [stem]
    if re.fullmatch(r'g[0-9]+', stem):
        # The ALCHIQ generator seeds gNNN keep their HermiT answers as NNN.json.
        stems.append(stem[1:])
    for p in [beside] + [os.path.join(d, x + '.json') for d in dirs for x in stems]:
        if os.path.exists(p):
            with open(p) as f:
                g = json.load(f)
            uns = {strip(c) for c in g['unsatisfiable']}
            subs = {(strip(a), strip(b)) for a, b in g['subsumptions']
                    if strip(a) not in uns and strip(b) not in uns and strip(a) != strip(b)}
            if not g['consistent']:
                return False, set(), set()
            return True, subs, uns
    return None


def run_one(km, checkers, out, timeout, mode, family, path, gold_dirs):
    key = hashlib.sha1((family + '\0' + path + '\0' + mode).encode()).hexdigest()[:12]
    tmp = os.path.join(out, 'tmp', key)
    os.makedirs(tmp, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
    env.update({'KM_THREADS': '1', 'KM_TIMING': '1', 'TMPDIR': tmp})
    if mode != 'off':
        env['KM_LEAN_CHECKERS'] = checkers
    if mode == 'ht':
        env['KM_LEAN_CHECKERS_HT'] = '1'
    if mode == 'all':
        env['KM_LEAN_CHECKERS_SET'] = 'all'
    t0 = time.monotonic()
    proc = subprocess.Popen([km, 'classify', '--lines', path], stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, env=env, text=True,
                            start_new_session=True)
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        status = 'ok' if proc.returncode == 0 else 'exit%d' % proc.returncode
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate()
        status = 'timeout'
    wall = time.monotonic() - t0
    subprocess.run(['rm', '-rf', tmp])
    events = []
    routes = []
    last_err = ''
    for line in stderr.splitlines():
        m = EVENT.match(line)
        if m:
            events.append({'status': m.group(1), 'family': m.group(2), 'checker': m.group(3),
                           'certificate': m.group(4), 'bytes': int(m.group(5)),
                           'detail': json.loads(m.group(7)) if m.group(7) else ''})
            continue
        r = ROUTE.search(line)
        if r:
            routes.append(r.group(1))
        if line.strip() and not line.startswith('KM_TIMING') and not line.startswith('KM_LEAN_CHECK'):
            last_err = line.strip()[:300]
    answer = parse_answer(stdout) if status == 'ok' else None
    digest = None
    if answer is not None:
        cons, subs, uns = answer
        digest = hashlib.sha256(json.dumps([cons, sorted(subs), sorted(uns)]).encode()).hexdigest()[:16]
    verdict = None
    gold = gold_answer(gold_dirs, path)
    if gold is not None and answer is not None:
        verdict = 'ok' if gold == answer else 'WRONG'
    return {'family': family, 'path': path, 'mode': mode, 'status': status,
            'wall_s': round(wall, 3), 'routes': routes, 'answer': digest,
            'gold': verdict, 'events': events,
            'stderr_last': last_err if status != 'ok' else ''}


def cmd_run(argv):
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--km', required=True)
    ap.add_argument('--checkers', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--timeout', type=float, default=60)
    ap.add_argument('--modes', default='off,on,ht')
    ap.add_argument('--gold', action='append', default=[])
    ap.add_argument('inputs', nargs='+')
    a = ap.parse_args(argv)
    os.makedirs(a.out, exist_ok=True)
    items = []
    for f in a.inputs:
        with open(f) as fh:
            for line in fh:
                line = line.rstrip('\n')
                if line and not line.startswith('#'):
                    family, path = line.split('\t', 1)
                    items.append((family, path))
    modes = a.modes.split(',')
    results = os.path.join(a.out, 'results.jsonl')
    done = set()
    if os.path.exists(results):
        with open(results) as fh:
            for line in fh:
                r = json.loads(line)
                done.add((r['family'], r['path'], r['mode']))
    todo = [(m, fam, p) for fam, p in items for m in modes if (fam, p, m) not in done]
    print(f'{len(items)} inputs, {len(modes)} modes, {len(todo)} runs to do', flush=True)
    with open(results, 'a') as out, cf.ThreadPoolExecutor(a.jobs) as pool:
        futures = [pool.submit(run_one, a.km, a.checkers, a.out, a.timeout, m, fam, p, a.gold)
                   for m, fam, p in todo]
        for n, fut in enumerate(cf.as_completed(futures), 1):
            out.write(json.dumps(fut.result()) + '\n')
            out.flush()
            if n % 50 == 0:
                print(f'{n}/{len(todo)}', flush=True)


def classify_record(r):
    """accepted / rejected / cannot_check for one checked run."""
    ev = r['events']
    if any(e['status'] == 'rejected' for e in ev):
        return 'rejected'
    if r['status'] != 'ok':
        return 'no_answer'
    if any(e['status'] == 'accepted' and e['certificate'] in PUBLICATION for e in ev):
        return 'accepted'
    return 'cannot_check'


def reason(r):
    ev = r['events']
    rej = [e for e in ev if e['status'] == 'rejected']
    if rej:
        return '; '.join(f"{e['checker']}: {e['detail']}" for e in rej)[:300]
    cc = [e for e in ev if e['status'] == 'cannot_check']
    if cc:
        return '; '.join(sorted({f"{e['family']}: {e['detail'][:120]}" for e in cc}))[:300]
    if r['status'] != 'ok':
        return r['status'] + ' ' + r.get('stderr_last', '')
    return 'no certificate emitted on this route'


def cmd_summarize(argv):
    out = argv[0]
    rows = [json.loads(l) for l in open(os.path.join(out, 'results.jsonl'))]
    by = {}
    for r in rows:
        by.setdefault((r['family'], r['path']), {})[r['mode']] = r
    modes = sorted({r['mode'] for r in rows}, key=lambda m: ['off', 'on', 'ht', 'all'].index(m))
    lines = []
    tsv = ['\t'.join(['family', 'input', 'route_off', 'status_off', 'wall_off', 'gold_off'] +
                     sum([[f'outcome_{m}', f'status_{m}', f'wall_{m}', f'same_answer_{m}',
                           f'checkers_{m}', f'reason_{m}'] for m in modes if m != 'off'], []))]
    from collections import Counter, defaultdict
    totals = {m: Counter() for m in modes if m != 'off'}
    per_family = {m: defaultdict(Counter) for m in totals}
    per_route = {m: defaultdict(Counter) for m in totals}
    per_checker = {m: defaultdict(Counter) for m in totals}
    changed = {m: [] for m in totals}
    rejections = {m: [] for m in totals}
    wall = {m: [0.0, 0.0, 0] for m in totals}
    gold = Counter()
    for (fam, path), rec in sorted(by.items()):
        off = rec.get('off')
        if off is None:
            continue
        route = off['routes'][-1] if off['routes'] else '-'
        if off.get('gold'):
            gold[off['gold']] += 1
        row = [fam, path, route, off['status'], str(off['wall_s']), off.get('gold') or '']
        for m in totals:
            r = rec.get(m)
            if r is None:
                row += [''] * 6
                continue
            o = classify_record(r)
            totals[m][o] += 1
            per_family[m][fam][o] += 1
            per_route[m][route][o] += 1
            for e in r['events']:
                per_checker[m][e['checker'] if e['checker'] != '-' else e['family'] + ':none'][e['status']] += 1
            same = ''
            if off['answer'] and r['answer']:
                same = 'yes' if off['answer'] == r['answer'] else 'NO'
                if same == 'NO':
                    changed[m].append(path)
                if off['status'] == 'ok' and r['status'] == 'ok':
                    wall[m][0] += off['wall_s']
                    wall[m][1] += r['wall_s']
                    wall[m][2] += 1
            if o == 'rejected':
                rejections[m].append((fam, path, reason(r)))
            ran = ','.join(sorted({f"{e['checker']}={e['status']}" for e in r['events']
                                   if e['checker'] != '-'}))
            row += [o, r['status'], str(r['wall_s']), same, ran, reason(r).replace('\t', ' ')]
        tsv.append('\t'.join(row))
    with open(os.path.join(out, 'per-input.tsv'), 'w') as fh:
        fh.write('\n'.join(tsv) + '\n')
    lines.append('# Checkers-on suite summary\n')
    lines.append(f'Inputs: {len(by)}. Off-mode answers against cached HermiT gold: {dict(gold)}.\n')
    for m in totals:
        lines.append(f'## Mode `{m}`\n')
        t = totals[m]
        lines.append('| outcome | runs |\n|---|---:|')
        for k in ('accepted', 'rejected', 'cannot_check', 'no_answer'):
            lines.append(f'| {k} | {t[k]} |')
        w = wall[m]
        if w[2]:
            lines.append(f'\nWall time on the {w[2]} inputs both modes answer: off {w[0]:.1f} s, '
                         f'{m} {w[1]:.1f} s (ratio {w[1] / max(w[0], 1e-9):.2f}).')
        lines.append(f"\nAnswers that differ from the unchecked run: {len(changed[m])}"
                     + (': ' + ', '.join(changed[m][:20]) if changed[m] else '') + '\n')
        for title, table in (('family', per_family[m]), ('route (off run)', per_route[m])):
            lines.append(f'### Per {title}\n')
            lines.append(f'| {title} | accepted | rejected | cannot_check | no_answer |\n|---|---:|---:|---:|---:|')
            for k in sorted(table):
                c = table[k]
                lines.append(f"| {k} | {c['accepted']} | {c['rejected']} | {c['cannot_check']} | {c['no_answer']} |")
            lines.append('')
        lines.append('### Per checker (events)\n')
        lines.append('| checker | accepted | rejected | cannot_check |\n|---|---:|---:|---:|')
        for k in sorted(per_checker[m]):
            c = per_checker[m][k]
            lines.append(f"| {k} | {c['accepted']} | {c['rejected']} | {c['cannot_check']} |")
        lines.append('')
        if rejections[m]:
            lines.append('### Rejections\n')
            lines.append('| family | input | checker message |\n|---|---|---|')
            for fam, path, why in rejections[m]:
                lines.append(f'| {fam} | `{os.path.basename(path)}` | {why} |')
            lines.append('')
    with open(os.path.join(out, 'summary.md'), 'w') as fh:
        fh.write('\n'.join(lines) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    if len(sys.argv) < 2 or sys.argv[1] not in ('run', 'summarize'):
        sys.exit(__doc__)
    {'run': cmd_run, 'summarize': cmd_summarize}[sys.argv[1]](sys.argv[2:])
