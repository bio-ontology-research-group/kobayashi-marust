import csv, json, os, re, sys, collections
from multiprocessing import Pool
TSV = "/mnt/data1/leechuck/km-work/wt/v1.6.1/results/agents/2026-11-10/v160-p3-rerun/data/p3-results.tsv"
OUT = "/mnt/data1/leechuck/km-work/v161/survey/per_input.jsonl"
WT = "/mnt/data1/leechuck/km-work/wt/v1.6.1/engine/tests/"
VOCAB = ("http://www.w3.org/2002/07/owl#", "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
         "http://www.w3.org/2000/01/rdf-schema#", "http://www.w3.org/2001/XMLSchema#")
STDP = {"owl", "rdf", "rdfs", "xsd", "_"}
LIT = re.compile(r'"(?:[^"\\]|\\.)*"', re.S)
HEAD = re.compile(r'\b([A-Z][A-Za-z]+)\(')
FULL = re.compile(r'<([^<>\s"]+)>')
PREF = re.compile(r'(?<![\w<:/#.-])([A-Za-z_][\w.-]*)?:([^\s()<>"=]+)')
PFX = re.compile(r'Prefix\(\s*([^\s:=()]*):?=\s*<([^>]*)>\s*\)')
HDR = re.compile(r'Prefix\([^)]*\)|Ontology\(\s*<[^>]*>(?:\s*<[^>]*>)?|Import\(\s*<[^>]*>\s*\)')
KEYS = ["topObjectProperty", "bottomObjectProperty", "topDataProperty", "bottomDataProperty", "owl:Thing", "owl:Nothing"]
CAP = 4_000_000

def survey(args):
    orig, path = args
    heads = collections.Counter(); kw = collections.Counter()
    prefixes = {}; F = set(); P = set(); nfull = npref = 0; capped = False
    first = True; carry = ""; size = os.path.getsize(path)
    with open(path, "r", encoding="latin1", newline="") as f:
        while True:
            blk = f.read(16 << 20)
            if not blk and not carry: break
            text = carry + blk
            if blk:
                cut = text.rfind("\n")
                if cut < 0: cut = text.rfind(" ")
                if cut < 0: carry = ""; cut = len(text) - 1
                else: carry = text[cut + 1:]
                text = text[:cut + 1]
            else:
                carry = ""
            if first:
                first = False
                for m in PFX.finditer(text[:2_000_000]): prefixes[m.group(1)] = m.group(2)
                kw["header_import"] = len(re.findall(r'\bImport\(', text))
                text = HDR.sub(" ", text)
            if '"' in text: text = LIT.sub('""', text)
            for h in HEAD.findall(text): heads[h] += 1
            for k in KEYS: kw[k] += text.count(k)
            for u in FULL.findall(text):
                if u.startswith(VOCAB): continue
                nfull += 1
                if len(F) < CAP: F.add(u)
                else: capped = True
            t2 = FULL.sub(" ", text)
            for p, l in PREF.findall(t2):
                if p in STDP: continue
                npref += 1
                if len(P) < CAP: P.add((p, l))
                else: capped = True
            if not blk: break
    mixed = 0
    if F and P:
        for p, l in P:
            base = prefixes.get(p)
            if base is not None and (base + l) in F: mixed += 1
    return dict(input=orig, path=path, size=size, heads=dict(heads), kw=dict(kw),
                prefixes=len(prefixes), prefix_names=sorted(prefixes)[:30], full_tokens=nfull, pref_tokens=npref,
                uniq_full=len(F), uniq_pref=len(P), mixed_entities=mixed, capped=capped)

def main():
    rows = list(csv.DictReader(open(TSV), delimiter="\t"))
    done = set()
    if os.path.exists(OUT):
        for l in open(OUT): done.add(json.loads(l)["input"])
    todo = []
    for r in rows:
        p = r["input"]
        if p in done: continue
        if not os.path.exists(p): p = WT + p.split("engine/tests/")[1]
        todo.append((r["input"], p))
    todo.sort(key=lambda x: -os.path.getsize(x[1]))
    with Pool(2) as pool, open(OUT, "a") as out:
        for i, res in enumerate(pool.imap_unordered(survey, todo, chunksize=1)):
            out.write(json.dumps(res) + "\n"); out.flush()
            if i % 100 == 0: print(i, len(todo), flush=True)
main()
