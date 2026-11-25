#!/usr/bin/env python3
"""produce.py NF_FILE HINT_OUT [--part J]: build a consistency hint for the
normal form printed by NFDump.lean. Prints one JSON line with the outcome.
"""
import json
import resource
import sys
import time

sys.setrecursionlimit(100000)

import nf as nfm
from finder import Finder, Fail, solve
import hintcheck


def produce(nfpath, out, part=0, comment=None, **kw):
    t0 = time.time()
    N = nfm.parse(nfpath)
    res = {'nf': nfpath, 'route': N.route, 'n': N.n, 'm': N.m, 'parts': len(N.parts)}
    if N.error or not N.parts:
        res.update(status='no-nf', reason=N.error or 'no parts')
        return res
    ix = nfm.Index(N, N.parts[part])
    res['clauses'] = len(N.parts[part].gci) + len(N.parts[part].ex) + len(N.parts[part].all) + \
        len(N.parts[part].ge) + len(N.parts[part].le)
    if ix.long_chains:
        res.update(status='fail', reason='chain of length > 1 in the normal form')
        return res
    try:
        F = solve(ix, **kw)
    except Fail as e:
        res.update(status='fail', reason=str(e), t_find=round(time.time() - t0, 2))
        return res
    h = F.hint()
    res.update(F.stats)
    res['t_find'] = round(time.time() - t0, 2)
    t1 = time.time()
    why = hintcheck.check(ix, h)
    res['t_selfcheck'] = round(time.time() - t1, 2)
    res['core'] = h.k
    res['recs'] = len(h.recs)
    if why:
        res.update(status='selfcheck-reject', reason=why)
    else:
        res['status'] = 'hint'
    hintcheck.write(h, out, comment)
    res['maxrss_mb'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024
    return res


if __name__ == '__main__':
    a = sys.argv[1:]
    part = 0
    if '--part' in a:
        i = a.index('--part')
        part = int(a[i + 1])
        del a[i:i + 2]
    print(json.dumps(produce(a[0], a[1], part)))
