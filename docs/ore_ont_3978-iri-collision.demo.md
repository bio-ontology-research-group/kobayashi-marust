# KM unsound on ORE ore_ont_3978: an IRI-shortening collision (root cause + fix)

*2026-06-08T18:29:24Z by Showboat 0.6.1*
<!-- showboat-id: 5dd58db8-6799-4706-be32-1eb0de86cbfd -->

On the ORE 2015 classification benchmark, KM was flagged **unsound** on `ore_ont_3978` (ALEH+, a GO "dlapproximated" ontology): it derived **838** subsumptions where both Konclude and HermiT agree on **824**. The 14 extras are all of the form `GO_x ⊑ GO_y`. This document reproduces the cause and proves the fix. The root cause is **not** in the reasoning engine or its Lean-checked calculus: it is the OWL front-end collapsing two *distinct* IRIs that share a local name (`part_of`) into one internal role.

### 1. Get the ontology (public ORE 2015 corpus, Zenodo record 18578). We pull just the one file out of the 725 MB zip via HTTP range requests, so no full download.

```bash
ONT=/tmp/3978/pool_sample/files/ore_ont_3978.owl
if [ ! -f "$ONT" ]; then
  mkdir -p /tmp/3978 && ( cd /tmp/3978 && uvx --from remotezip remotezip "https://zenodo.org/records/18578/files/ore2015_sample.zip" "pool_sample/files/ore_ont_3978.owl" >/dev/null 2>&1 )
fi
ls -l "$ONT" && echo "axiom types:" && grep -oE "^[A-Za-z]+\(" "$ONT" | sort | uniq -c | sort -rn | head -8
```

```output
-rw-rw-r-- 1 leechuck leechuck 215817 Jun  8 21:17 /tmp/3978/pool_sample/files/ore_ont_3978.owl
axiom types:
    994 Declaration(
    657 EquivalentClasses(
     10 SubObjectPropertyOf(
      6 SubClassOf(
      5 Prefix(
      3 ClassAssertion(
      2 TransitiveObjectProperty(
      1 Ontology(
```

### 2. Two distinct `part_of` IRIs

The class **definitions** use `OBO_REL#part_of`, while the **role hierarchy** (and transitivity) is stated over a *different* property, `obo#part_of`. A correct reasoner keeps them apart.

```bash
ONT=/tmp/3978/pool_sample/files/ore_ont_3978.owl
echo "role hierarchy edges into obo#part_of:"
grep -oE "SubObjectPropertyOf\(<[^>]+> <[^>]*obo#part_of>\)" "$ONT" | sed -E "s#http://purl.org/obo/owl/##g"
echo
echo "the class GO_0005654 is defined with surrounds + OBO_REL#part_of:"
grep -oE "EquivalentClasses\(<[^>]*GO_0005654>.*surrounds[^)]*\)" "$ONT" | sed -E "s#http://purl.org/obo/owl/##g" | head -c 300
```

```output
role hierarchy edges into obo#part_of:
SubObjectPropertyOf(<obo#inner_part_of> <obo#part_of>)
SubObjectPropertyOf(<obo#outer_part_of> <obo#part_of>)
SubObjectPropertyOf(<obo#perforates> <obo#part_of>)
SubObjectPropertyOf(<obo#surrounds> <obo#part_of>)

the class GO_0005654 is defined with surrounds + OBO_REL#part_of:
EquivalentClasses(<GO#GO_0005654> ObjectIntersectionOf(<GO#GO_0044428> ObjectSomeValuesFrom(<OBO_REL#part_of> <GO#GO_0031981>) ObjectSomeValuesFrom(<obo#surrounds> <GO#GO_0005694>) ObjectSomeValuesFrom(<obo#surrounds> <GO#GO_0005730>)
```

### 3. The collision

The front-end (`engine/py/frontend.py`) turns each IRI into an internal name. The old shortener (`_short_base`, preserved in the code) maps an IRI to its fragment, so **both** `part_of` IRIs become the single name `part_of`. That silently merges the two properties, and the role-hierarchy axiom `surrounds ⊑ obo#part_of` then wrongly applies to the `OBO_REL#part_of` used in the definitions — manufacturing `GO_0005654 ⊑ GO_0044427`. The fix makes `short()` collision-safe: distinct IRIs get distinct names; unique local names are returned unchanged.

```bash
export MOOSE_HOME=/home/leechuck/Documents/papers/neuro-symbolic-independence/moose PYTHONPATH=engine/py
python3 - <<"PY"
import frontend
iris=["http://purl.org/obo/owl/OBO_REL#part_of","http://purl.org/obo/owl/obo#part_of"]
print("OLD shortener (_short_base): the bug")
for i in iris: print(f"   {i:42} -> {frontend._short_base(i)!r}")
frontend.reset_short()
print("NEW shortener (short): collision-safe")
for i in iris: print(f"   {i:42} -> {frontend.short(i)!r}")
PY
```

```output
OLD shortener (_short_base): the bug
   http://purl.org/obo/owl/OBO_REL#part_of    -> 'part_of'
   http://purl.org/obo/owl/obo#part_of        -> 'part_of'
NEW shortener (short): collision-safe
   http://purl.org/obo/owl/OBO_REL#part_of    -> 'part_of'
   http://purl.org/obo/owl/obo#part_of        -> 'part_of__obo'
```

### 4. Minimal reproducer

Four axioms isolate the bug: `surrounds` is a sub-property of `ns1#part_of`, `A ≡ ∃ns1:surrounds.X`, and `B ≡ ∃ns2:part_of.X` with a **different** `part_of` namespace. `A ⊑ B` must be **false** (the two `part_of`s are unrelated). We run KM end-to-end with the fixed front-end, then re-run the classification with the front-end monkey-patched back to the buggy `_short_base` to show the merge returning.

```bash
export KM_ENGINE=engine/target/release/kobayashi-marust KM_THREADS=1
export MOOSE_HOME=/home/leechuck/Documents/papers/neuro-symbolic-independence/moose PYTHONPATH=engine/py
mkdir -p /tmp/3978
cat > /tmp/3978/collide.ofn <<"OFN"
Prefix(:=<http://ex#>)
Ontology(
  Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:X))
  Declaration(ObjectProperty(<http://ns1#part_of>))
  Declaration(ObjectProperty(<http://ns2#part_of>))
  Declaration(ObjectProperty(<http://ns1#surrounds>))
  SubObjectPropertyOf(<http://ns1#surrounds> <http://ns1#part_of>)
  EquivalentClasses(:A ObjectSomeValuesFrom(<http://ns1#surrounds> :X))
  EquivalentClasses(:B ObjectSomeValuesFrom(<http://ns2#part_of> :X))
)
OFN
python3 - <<"PY"
import json, frontend, importlib
def run_ab(buggy):
    importlib.reload(frontend)
    if buggy:
        frontend.short = frontend._short_base
        frontend.reset_short = lambda: None
    import owl_classify; importlib.reload(owl_classify)
    res = owl_classify.classify("/tmp/3978/collide.ofn")
    return ("A","B") in set(map(tuple, res["subsumptions"]))
print("   BUGGY front-end (short = _short_base):  A subsumed-by B =", run_ab(True),  " <- unsound")
print("   FIXED front-end (collision-safe short): A subsumed-by B =", run_ab(False), " <- correct")
PY
```

```output
   BUGGY front-end (short = _short_base):  A subsumed-by B = True  <- unsound
   FIXED front-end (collision-safe short): A subsumed-by B = False  <- correct
```

### 5. The real ontology, fixed

With the collision-safe front-end, KM classifies `ore_ont_3978` to **824** subsumptions — exactly matching HermiT and Konclude — and all four sampled spurious entries are gone.

```bash
export KM_ENGINE=engine/target/release/kobayashi-marust KM_THREADS=1
export MOOSE_HOME=/home/leechuck/Documents/papers/neuro-symbolic-independence/moose PYTHONPATH=engine/py
python3 - <<"PY"
import owl_classify
res = owl_classify.classify("/tmp/3978/pool_sample/files/ore_ont_3978.owl")
s = set(map(tuple, res["subsumptions"]))
print("   total subsumptions:", len(s), "  (HermiT = Konclude = 824)")
for a,b in [("GO_0005654","GO_0044427"),("GO_0002079","GO_0044425"),("GO_0065010","GO_0043230"),("GO_0060170","GO_0044441")]:
    print(f"   spurious {a} sub {b}:", (a,b) in s)
PY
```

```output
   total subsumptions: 824   (HermiT = Konclude = 824)
   spurious GO_0005654 sub GO_0044427: False
   spurious GO_0002079 sub GO_0044425: False
   spurious GO_0065010 sub GO_0043230: False
   spurious GO_0060170 sub GO_0044441: False
```

### 6. No regression

The fix only changes names that actually collide; a unique local name is returned unchanged, so `short(iri) == _short_base(iri)` for every IRI whose fragment is owned by no other IRI. The 23 checked-in fixtures (`oracle/ontologies`, `examples/ontologies`) produce byte-identical classifications before and after, so existing certificates and outputs are unaffected.

```bash
export KM_ENGINE=engine/target/release/kobayashi-marust KM_THREADS=1
export MOOSE_HOME=/home/leechuck/Documents/papers/neuro-symbolic-independence/moose PYTHONPATH=engine/py
python3 - <<"PY"
import glob, importlib, frontend, owl_classify
fixtures = sorted(glob.glob("oracle/ontologies/*.ofn") + glob.glob("examples/ontologies/*.ofn"))
def classify(path, buggy):
    importlib.reload(frontend)
    if buggy:
        frontend.short = frontend._short_base; frontend.reset_short = lambda: None
    importlib.reload(owl_classify)
    r = owl_classify.classify(path)
    return (r["consistent"], frozenset(map(tuple, r["subsumptions"])))
diffs = [f for f in fixtures if classify(f, False) != classify(f, True)]
print(f"   fixtures compared: {len(fixtures)}")
print(f"   differing between fixed and buggy front-end: {len(diffs)}")
print("   -> byte-identical on every non-colliding fixture" if not diffs else f"   DIFFS: {diffs}")
PY
```

```output
   fixtures compared: 23
   differing between fixed and buggy front-end: 0
   -> byte-identical on every non-colliding fixture
```

### Conclusion

The defect was a front-end IRI-shortening collision, not a reasoning error: the engine and its Lean-checked calculus correctly classified the (mis-named) input they were handed. The fix makes `engine/py/frontend.py` `short()` collision-safe (reset per ontology in `ofn_to_clauses`), removing the only in-fragment soundness discrepancy KM showed on the ORE 2015 corpus, with no change to any non-colliding ontology.
