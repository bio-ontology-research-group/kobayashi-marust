import sys
src, dst = sys.argv[1], sys.argv[2]
t = open(src, encoding='utf-8').read()
out = []; i = 0; key = 'DataPropertyAssertion('
while True:
    j = t.find(key, i)
    if j < 0: out.append(t[i:]); break
    if j > 0 and t[j-1] not in '\n \t': out.append(t[i:j+1]); i = j+1; continue
    out.append(t[i:j]); k = j + len(key); depth = 1; inq = False
    while depth:
        c = t[k]
        if inq:
            if c == '\\': k += 1
            elif c == '"': inq = False
        elif c == '"': inq = True
        elif c == '(': depth += 1
        elif c == ')': depth -= 1
        k += 1
    i = k
open(dst, 'w', encoding='utf-8').write(''.join(out))
