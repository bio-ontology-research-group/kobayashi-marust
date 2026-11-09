"""Pair two ore_time.sh runs: identical signatures, rc changes, time ratios.
usage: python3 -I ore_pair.py DIR BASE_TAG NEW_TAG"""
import csv, gzip, statistics, sys
d, A, B = sys.argv[1:4]
def load(t): return {r[0]: r for r in csv.reader(open(f'{d}/times-{t}.tsv'), delimiter='\t') if r[0] != 'DONE'}
a, b = load(A), load(B)
both = same = 0; diffs = []; rc = []; ratios = []
for n in a:
    if n not in b: continue
    ra, rb = a[n], b[n]
    if ra[2] == '0' and rb[2] == '0':
        both += 1
        if gzip.open(f'{d}/out-{A}/{n}.sig.gz').read() == gzip.open(f'{d}/out-{B}/{n}.sig.gz').read(): same += 1
        else: diffs.append(n)
        if float(ra[3]) > 1: ratios.append(float(rb[3]) / float(ra[3]))
    elif ra[2] != rb[2]: rc.append((n, ra[2], rb[2], round(float(ra[3]), 1), round(float(rb[3]), 1)))
print(f'inputs {len(a)} both-answered {both} identical {same} differ {diffs}')
print('answer-status changes', rc)
if ratios: print(f'time ratio new/base over {len(ratios)} inputs above 1 s: mean {statistics.mean(ratios):.3f} median {statistics.median(ratios):.3f} max {max(ratios):.2f}')
print('route changes', [(n, a[n][4], b[n][4]) for n in a if n in b and a[n][4] != b[n][4]])
