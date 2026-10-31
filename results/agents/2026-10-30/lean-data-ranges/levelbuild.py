"""Build the ContextCalculus library by import level, at most CHUNK modules
per lake call (the host's commit limit makes a fully parallel lake build fail
with ENOMEM). Retries a chunk on resource errors."""
import os, re, subprocess, sys
root, chunk = sys.argv[1], int(sys.argv[2])
os.chdir(root)
def deps(mod):
    out = []
    for line in open(mod.replace('.', '/') + '.lean'):
        m = re.match(r'\s*import\s+(\S+)', line)
        if m and m.group(1).startswith('ContextCalculus'):
            out.append(m.group(1))
    return out
level = {}
sys.setrecursionlimit(10000)
def lv(m):
    if m not in level:
        level[m] = 1 + max([lv(d) for d in deps(m)], default=-1)
    return level[m]
lv('ContextCalculus')
env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
for L in range(max(level.values()) + 1):
    mods = sorted(m for m in level if level[m] == L)
    for i in range(0, len(mods), chunk):
        part = mods[i:i + chunk]
        for attempt in range(8):
            r = subprocess.run(['lake', 'build'] + part, capture_output=True, text=True, env=env)
            if r.returncode == 0:
                break
            text = r.stdout + r.stderr
            if 'resource exhausted' not in text and 'create thread' not in text and 'code 134' not in text:
                print('FAIL', part); print(text[-4000:]); sys.exit(1)
        else:
            print('FAIL (resources)', part); sys.exit(1)
    print('level', L, len(mods), flush=True)
print('modules', len(level), 'ok')
