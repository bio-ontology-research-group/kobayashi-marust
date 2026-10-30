import sys, os, collections
mot = dict(l.split() for l in open(sys.argv[2]))
c = collections.Counter()
for l in open(sys.argv[1]):
    t = l.rstrip('\n').split('\t')
    c[(mot[os.path.basename(t[0])[:-4]], t[2])] += 1
for m in sorted({k[0] for k in c}):
    print(m, {v: n for (mm, v), n in c.items() if mm == m})
