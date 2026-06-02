# Validation Oracle (HermiT)

Ground-truth reasoning results for checking our own SROIQ reasoner. Given any
OWL ontology, this oracle classifies it with the **HermiT** reasoner (via the
OWL API) and emits JSON describing consistency, the inferred atomic class
hierarchy, and the unsatisfiable named classes.

## Contents

- `Oracle.java` — small program: load ontology, classify with HermiT, print JSON.
- `run_oracle.sh <ontology-file>` — entry point. Builds the classpath, compiles
  `Oracle.java` (once), and runs it. Prints JSON to **stdout**; reasoner/SLF4J
  noise goes to **stderr**.
- `results/` — saved JSON for the four benchmark ontologies.

The committed `results/` JSON is the reference oracle output, so the cross-check
in `validate.py` is reproducible **without** rebuilding HermiT. The steps below
are only needed to regenerate it.

## Prerequisites (one-time)

HermiT is an **external** dependency (not vendored here). Obtain a HermiT build
(OpenJDK 21 + Maven 3.9 assumed) and point `HERMIT_DIR` at it:

```bash
export HERMIT_DIR=/path/to/hermit-reasoner
JAVA_HOME=/usr/lib/jvm/java-21-openjdk-amd64 \
  ( cd "$HERMIT_DIR" && mvn -q -DskipTests -Dmaven.javadoc.skip=true -Dgpg.skip=true package )
```

This produces `$HERMIT_DIR/target/org.semanticweb.hermit-*.jar` and pulls in the
OWL API. (Skipping javadoc/gpg avoids a javadoc-plugin failure under JDK 21.)

## Usage

```bash
./run_oracle.sh /path/to/ontology.ofn        # or .owl, .ttl, .rdf — anything the OWL API parses
```

The script auto-detects `JAVA_HOME` (defaults to
`/usr/lib/jvm/java-21-openjdk-amd64`; override by exporting `JAVA_HOME`),
caches the dependency classpath in `.classpath.txt`, and recompiles
`Oracle.java` if it changed.

To (re)generate the saved benchmark results:

```bash
ONT=../examples/ontologies
./run_oracle.sh $ONT/disjunction.ofn               > results/disjunction.json
./run_oracle.sh $ONT/kinship.ofn                   > results/kinship.json
./run_oracle.sh $ONT/kinship_chain.ofn             > results/kinship_chain.json
./run_oracle.sh ontologies/trans_test.ofn          > results/trans_test.json
```

Then `python3 validate.py` compares this engine's verdicts against the oracle.

## Output format

```json
{
  "ontology": "<file name>",
  "consistent": true,
  "subsumptions": [ ["SubFragment", "SuperFragment"], ... ],
  "unsatisfiable": [ "ClassFragment", ... ]
}
```

- **`consistent`** — `isConsistent()` from HermiT.
- **`subsumptions`** — all entailed atomic `A ⊑ B` over **named** classes
  (direct + indirect, i.e. the full transitively-closed hierarchy).
  Equivalences appear as **mutual** subsumptions (both `[A,B]` and `[B,A]`).
  Excluded: `X ⊑ X`, `X ⊑ owl:Thing`, and anything involving `owl:Nothing`.
  Unsatisfiable classes are skipped here and listed separately.
- **`unsatisfiable`** — named classes equivalent to `owl:Nothing`.

Class names are reported as short fragments (after `#`, else after the last
`/`). Within a single ontology these are unambiguous.
