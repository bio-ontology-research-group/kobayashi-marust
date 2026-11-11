#!/usr/bin/env python3
"""Synthetic EL clause stream for km-el-reference (v161-stack).

usage: gen_synth_clauses.py <n_clauses> <k_concept_blocks> <out.json>

Ten-cycle of every recognised EL clause shape (nf1, nf2, n-ary conjunction,
nf3 role and filler halves with a fresh Skolem function per pair, nf4, nf6,
nf7, nf5, binary bottom).  Concept ids are taken modulo k blocks, so the
closure stays linear in k while the clause count grows to n.  `named` holds
one concept per nf1 block (k/10 names).
"""
import sys

n, k, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
assert k % 10 == 0


def var(v):
    return '{"kind":"var","name":"%s"}' % v


def c(a, t="x"):
    return '{"kind":"concept","concept":"C%d","term":%s}' % (a, var(t) if t in ("x", "y", "z") else t)


def r(name, s, t):
    return '{"kind":"role","role":"%s","source":%s,"target":%s}' % (name, var(s), t if t.startswith("{") else var(t))


def fn(f):
    return '{"kind":"fun","function":"f%d","arg":%s}' % (f, var("x"))


def clause(i):
    j = i % k
    a = 3 * j
    m = i % 10
    if m == 0:
        b, h = [c(a)], [c(a + 1)]
    elif m == 1:
        b, h = [c(a), c(a + 1)], [c(a + 2)]
    elif m == 2:
        b, h = [c(a), c(a + 1), c(a + 2), c(a + 3)], [c(a + 4)]
    elif m == 3:
        b, h = [c(a)], [r("R1", "x", fn(i))]
    elif m == 4:
        a0 = 3 * ((i - 1) % k)
        b, h = [c(a0)], [c(a + 1, fn(i - 1))]
    elif m == 5:
        b, h = [r("R1", "x", "y"), c(a, "y")], [c(a + 1)]
    elif m == 6:
        b, h = [r("S%d" % j, "x", "y")], [r("T%d" % j, "x", "y")]
    elif m == 7:
        b, h = [r("R1", "x", "y"), r("R2", "y", "z")], [r("R3", "x", "z")]
    elif m == 8:
        b, h = [c(a)], []
    else:
        b, h = [c(a), c(a + 1)], []
    return '{"body":[%s],"head":[%s]}' % (",".join(b), ",".join(h))


with open(out, "w") as f:
    named = ['"C%d"' % (3 * j) for j in range(0, k, 10)]
    f.write('{"named":[%s],"clauses":[' % ",".join(named))
    buf = []
    first = True
    for i in range(n):
        buf.append(clause(i))
        if len(buf) == 10000 or i == n - 1:
            f.write(("" if first else ",") + ",".join(buf))
            first = False
            buf = []
    f.write("]}\n")
