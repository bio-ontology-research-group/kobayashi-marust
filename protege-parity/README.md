# protege-parity

Acceptance instrument for the goal "the KM plugin supports in Protégé everything HermiT supports".
It runs HermiT 1.4.3.456 (the Protégé 5 jar, `ignoreUnsupportedDatatypes = true`) and the KM plugin
through the OWL API 4.5.29 on real ontologies, asks both every `OWLReasoner` method over a seeded
sample of the signature, and writes a parity scoreboard (`PARITY.md`). Rerun it after each work package.

The module is separate from `../protege`, so the plugin jar does not change. It loads
`org.bioontology.kobayashimarust.protege.KMReasonerFactory` by name from
`../protege/target/protege5/classes`; nothing here is compiled against the plugin.

## Run

```bash
export TMPDIR=<scratch dir, not /tmp>
export MVN=<path to mvn>        # default: mvn on PATH
export KM_BIN=<path to km>      # the executable the plugin runs (needs --realize and --properties)
export PARITY_TMP=$TMPDIR
./run_parity.sh ontologies.txt <out dir>                 # 40 corpus ontologies plus W3C wine and food
PARITY_OPTS="--timeout 120 --sample 200" ./run_parity.sh a.owl b.owl <out dir>
./parity_report.py <out dir> PARITY.md --census census-per-input.tsv --diff-tsv diffs.tsv
./parity_adjudication.py <out dir> adjudication.md       # then append it to PARITY.md
./parity_show.py <out dir>/<ontology>.json '<text of a call id>'
```

`run_parity.sh` builds the plugin classes and this module with `mvn -o` (set `SKIP_BUILD=1` to skip), then
runs one ontology at a time. Per ontology `ParityRun` starts one JVM per reasoner (HermiT first, then KM),
each with a wall budget (`--timeout`, default 120 s, in the runs reported 180 s) and a cap on single
queries after precompute (`--call-timeout`, default 20 s). A reasoner that hangs is killed and its missing
answers count as timeouts. `KM_THREADS=1` is set for the workers.

## What it asks

Every method of `OWLReasoner` (OWL API 4.5.29) in these groups: metadata and lifecycle; `isConsistent`;
`precomputeInferences` and `isPrecomputed` for every `InferenceType`; class hierarchy, equivalents,
disjoint classes, satisfiability, instances for up to 200 classes (a seeded sample otherwise); the same
for 16 generated anonymous class expressions (complement, conjunction, disjunction, some, all, inverse
some, min cardinality, has value, one-of, data some); object property hierarchy, inverses, disjoint,
domains and ranges for named and inverse properties and the top and bottom property; data property
hierarchy, domains and disjoint; types, same, different individuals; object and data property values;
`isEntailed` for up to 5 axioms per `AxiomType` (3 taken from the ontology, 2 generated); and one set
of two axioms. A few queries that cost HermiT one tableau test per entity (disjoint, different
individuals) are asked for 6 entities only.

Answers are canonicalised: sets of IRIs, and nodes as sorted lists of IRIs. Node set answers are compared
by content (the flat entity set) and by structure (the grouping), and the verdict says which differs.

## Verdicts and the score

Per call: `agree`, `differ_content`, `differ_structure`, `km_unsupported` (KM threw, HermiT answered),
`km_timeout` (KM timed out or was not reached), `hermit_error` (HermiT threw, KM answered),
`both_error_same` (counts as agreement), `both_error_different`, `both_failed`, `hermit_timeout`
(left out of the score). `km_unsupported` also covers the three calls that report what KM can do: `isEntailmentCheckingSupported`
or `isPrecomputed` false where HermiT says true, and a `getPrecomputableInferenceTypes` that is a strict
subset of HermiT's. `getTimeOut` is informational (HermiT gets its own `Configuration` here and reports -1).
`parity_reverdict.py <out dir>` applies these rules to result files written before a rule existed.
A cell is one method on one ontology. The parity score is the share of cells
where KM agrees on every call, or HermiT fails on the whole cell and KM answers. The report also gives
a lenient score (grouping-only differences agree) and an adjusted score (also ignoring differences that
consist only of `owl:Thing`, `owl:Nothing` or the top and bottom properties).

## Not covered

See the end of `PARITY.md` ("What the harness does not cover").
