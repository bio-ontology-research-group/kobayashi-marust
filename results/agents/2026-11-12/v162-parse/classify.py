"""Classify the 1,781 survey inputs into F / non-F exactly as the survey's
aggregate.py does (row x1, "F4 + trans + chains"), resolve the paths of the
removed worktree, and write inputs.tsv (path, size, inF)."""
import csv, os, sys
SURVEY = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "v162-owl-survey", "per_input.tsv")
OLD = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-checkers-on-suite/"
NEW = "/mnt/data1/leechuck/km-work/wt/v1.6.2/"
IGN = {"Prefix","Ontology","Declaration","Class","ObjectProperty","DataProperty","NamedIndividual","AnnotationProperty","Datatype",
       "Annotation","AnnotationAssertion","SubAnnotationPropertyOf","AnnotationPropertyDomain","AnnotationPropertyRange"}
F1 = {"SubClassOf","EquivalentClasses","ObjectIntersectionOf","ObjectSomeValuesFrom","ObjectPropertyDomain","DisjointClasses"}
F3 = F1 | {"ObjectUnionOf","ObjectComplementOf","ObjectAllValuesFrom","ObjectPropertyRange"}
HI = {"SubObjectPropertyOf","EquivalentObjectProperties","InverseObjectProperties","ObjectInverseOf","SymmetricObjectProperty"}
F = F3 | HI | {"TransitiveObjectProperty","ObjectPropertyChain"}
META = {"input","size","p2_status","route","prefixes","full_tokens","pref_tokens","mixed_entities"}
out = csv.writer(open(sys.argv[1], "w"), delimiter="\t", lineterminator="\n")
out.writerow(["path","size","inF","p2_status"])
n = nf = 0
for r in csv.DictReader(open(SURVEY), delimiter="\t"):
    heads = {k for k, v in r.items() if k not in META and not k.startswith("kw_") and int(v) > 0}
    used = heads - IGN
    top = int(r["kw_topObjectProperty"]) + int(r["kw_bottomObjectProperty"]) > 0
    inside = (not r["input"].endswith(".ttl")) and used <= F and not top and int(r["kw_header_import"]) == 0
    path = r["input"].replace(OLD, NEW) if r["input"].startswith(OLD) else r["input"]
    if not os.path.exists(path):
        print("missing", path, file=sys.stderr)
    out.writerow([path, r["size"], int(inside), r["p2_status"]])
    n += 1; nf += inside
print(n, "inputs,", nf, "in F")
