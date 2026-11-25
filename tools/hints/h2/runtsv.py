import subprocess, sys, os, shlex
R = sys.argv[1]; d = sys.argv[2]
ok = bad = 0
for line in open(os.path.join(d, 'expected.tsv')):
    if line.startswith('#') or not line.strip(): continue
    parts = line.rstrip('\n').split('\t')
    f, args, exp = parts[0], parts[1], parts[2].strip()
    proc = 'sroiq-hint'
    if args.startswith('(sroiq-c2a)'):
        proc = 'sroiq-c2a'; args = args[len('(sroiq-c2a)'):].strip()
    a = []
    for w in args.split():
        a.append(w.replace('#', ' ') if a and a[-1] == '--row' else w)
    r = subprocess.run([R, '--procedure', proc] + a + [f], cwd=d, capture_output=True, text=True, timeout=300)
    out = ' '.join((r.stdout + ' ' + r.stderr).split())
    if out == ' '.join(exp.split()):
        ok += 1
    else:
        bad += 1; print('DIFF', f, args, '\n  got:', out[:300], '\n  exp:', exp[:300])
print('ok', ok, 'bad', bad)
