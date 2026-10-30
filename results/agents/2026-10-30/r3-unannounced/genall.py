import sys, importlib.util, os
here = os.path.dirname(os.path.abspath(__file__))
def load(n):
    spec = importlib.util.spec_from_file_location(n, os.path.join(here, n + '.py'))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
g, t = load('gen_r3'), load('gen_tpl')
out = sys.argv[1]
for i in range(3000):
    open(f'{out}/seeds/r{i}.ofn', 'w').write(g.gen(i, inverse=True))
for i in range(3000, 4000):
    open(f'{out}/seeds/r{i}.ofn', 'w').write(g.gen(i, inverse=False))
with open(f'{out}/tpl/motifs.tsv', 'w') as mf:
    for i in range(2000):
        text, m = t.gen(i)
        open(f'{out}/tpl/t{i}.ofn', 'w').write(text)
        mf.write(f't{i}\t{m}\n')
with open(f'{out}/tpl2/motifs.tsv', 'w') as mf:
    for i in range(1000):
        text, m = t.gen(i, family2=True)
        open(f'{out}/tpl2/u{i}.ofn', 'w').write(text)
        mf.write(f'u{i}\t{m}\n')
