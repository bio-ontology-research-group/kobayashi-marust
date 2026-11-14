# Kobayashi-MaRust Protégé plugin

This module provides a Protégé Desktop reasoner plugin for KM. It appears in
the **Reasoner** menu as **Kobayashi-MaRust** and supplies the inferred named
class hierarchy, equivalence classes, unsatisfiable classes, and ontology
consistency.

The plugin answers class and individual queries; see
[What the reasoner answers](#what-the-reasoner-answers). The object property
hierarchy, inverses, domains and ranges are answered; property assertion
queries are not yet exposed through the OWL API.
The bundle also contains an OWL Explanation API
`ExplanationGenerator` and `ExplanationGeneratorFactory` (OWL Explanation
2.0.1 in the Protégé 5 jar, 5.0.1 in the Protégé 6 jar). It returns verified,
source-axiom justifications for named-class entailments through KM's native
schema-2 protocol. See
[`docs/EXPLANATIONS.md`](../docs/EXPLANATIONS.md) for supported entailments,
bounds, and the Protégé explanation panel.

## Two builds

| Jar | Protégé | OWL API | OWL Explanation |
| --- | --- | --- | --- |
| `kobayashi-marust-protege5-<version>.jar` | 5.6.x | 4.5.29 | 2.0.1 |
| `kobayashi-marust-protege6-<version>.jar` | 6.0.0-alpha-1 and later | 5.5.1 | 5.0.1 |

Protégé 6 moved to OWL API 5 and does not load plugins built for Protégé 5,
so use the jar that matches your Protégé. Both jars come from the same
sources and have the same OSGi identity (`org.bioontology.kobayashi-marust`,
version equal to the KM version). Each release attaches both jars to its
[GitHub release](https://github.com/bio-ontology-research-group/kobayashi-marust/releases).

## Requirements

- Protégé Desktop 5.6.x or Protégé 6.
- Java 11 or newer.
- Nothing else on Linux (x86_64, aarch64), macOS (Intel, Apple silicon) or
  Windows (x86_64): the release jars bundle the native `km` executable for
  these platforms. Python and `moose` are not required.

The Protégé 5 build pins OWLAPI 4.5.29, OWL Explanation 2.0.1, its telemetry
2.0.0 runtime, Protégé 5.6.6, and Gson 2.11.0. The Protégé 6 build pins OWLAPI
5.5.1, OWL Explanation 5.0.1, telemetry 5.0.0, Protégé 6.0.0-alpha-1, Gson
2.11.0 and HPPC-RT 0.7.5. Protégé and OWLAPI packages are provided by the host
application; the bundle embeds the explanation runtime dependencies, Gson and,
for Protégé 6, HPPC-RT.
The embedded OWL Explanation and telemetry JARs remain intact with their
upstream LGPL 3 license metadata; Gson and HPPC-RT are Apache-2.0; KM's own
code remains BSD-3-Clause.

## What the reasoner answers

| OWL API call | Answer |
| --- | --- |
| `isConsistent`, `isSatisfiable`, `getUnsatisfiableClasses` | for named classes |
| `getTopClassNode`, `getBottomClassNode`, `getSuperClasses`, `getSubClasses`, `getEquivalentClasses` | the inferred named-class hierarchy, with HermiT's conventions for `owl:Thing` and `owl:Nothing` (below) |
| `getDisjointClasses(C)` | for `owl:Thing` (only the bottom node), `owl:Nothing` or an unsatisfiable class (every node) and a class outside the signature (only the bottom node); other classes throw |
| `getTypes(ind, direct)` | the named classes the individual belongs to, as class nodes, with `owl:Thing` as HermiT reports it; `direct` keeps the most specific nodes |
| `getInstances(C, direct)` | for a named class `C`: the individuals that are instances of `C` (direct: those whose most specific types include `C` or a class equivalent to it), one node per individual under the default `BY_NAME` policy and one node per same-individual group under `BY_SAME_AS`; an anonymous class expression throws |
| `getSameIndividuals(ind)` | the entailed equalities (`SameIndividual`, functional and inverse-functional roles, cardinality, nominals, any other entailment) |
| `getSubObjectProperties`, `getSuperObjectProperties` (direct or not), `getEquivalentObjectProperties`, `getInverseObjectProperties`, `getTopObjectPropertyNode`, `getBottomObjectPropertyNode` | the inferred object property hierarchy, for named properties and `ObjectInverseOf` expressions. Equivalent expressions share a node as in HermiT (`r` and an equivalent `s⁻` in one node; empty properties in the bottom node, universal ones in the top node). |
| `getObjectPropertyDomains`, `getObjectPropertyRanges` (direct or not) | the entailed named domains and ranges of a property or an inverse expression; an empty property has every class, direct answer `owl:Nothing` |
| `getDisjointObjectProperties(p)` | for `owl:topObjectProperty` and universal properties (the bottom node), `owl:bottomObjectProperty` and empty properties (every node) and properties outside the signature (the bottom node); other properties throw |
| `getSubDataProperties`, `getSuperDataProperties`, `getEquivalentDataProperties`, `getTopDataPropertyNode`, `getBottomDataPropertyNode`, `getDataPropertyDomains`, `getDisjointDataProperties` | for an ontology whose data properties occur only in sub-property, equivalence, assertion, functionality, domain (named class) and range (built-in datatype) axioms: the data property hierarchy and the named domains, computed in Java from those axioms and the class hierarchy ([`DataPropertyModel`](src/main/java/org/bioontology/kobayashimarust/protege/DataPropertyModel.java) explains why that is complete). Any other ontology throws `UnsupportedOperationException`. `getDisjointDataProperties` is answered for `owl:topDataProperty`, `owl:bottomDataProperty`, empty properties and properties outside the signature only. |
| `isEntailed` | declarations and annotation axioms (always true, as in HermiT); `SubClassOf` between named classes, `ClassAssertion` of a named class, `SameIndividual` of named individuals, `SubObjectPropertyOf` (no chains), `EquivalentObjectProperties`, `InverseObjectProperties`, `SymmetricObjectProperty`, `ObjectPropertyDomain` and `ObjectPropertyRange` with a named class |
| `getPrecomputableInferenceTypes` | `CLASS_HIERARCHY`, `OBJECT_PROPERTY_HIERARCHY`, `CLASS_ASSERTIONS`, `SAME_INDIVIDUAL`, and `DATA_PROPERTY_HIERARCHY` when the ontology is inside the data property fragment. HermiT also lists `OBJECT_PROPERTY_ASSERTIONS`; KM does not compute it, so Protégé does not ask for it. |

Classification costs the same as before. The individual queries use
`km classify --realize` ([`docs/REALIZATION.md`](../docs/REALIZATION.md)). The
plugin runs it once, on the first individual query or when Protégé asks to
precompute `CLASS_ASSERTIONS` or `SAME_INDIVIDUAL`, on the ontology revision
the class hierarchy was built from. It caches the answer and drops it when the
ontology changes and the reasoner flushes, so the next individual query runs
KM again. The incremental session cannot realize, so each realization is a
separate one-shot `km classify --realize` run; it takes about as long as a
full classification of the ontology with one extra class per individual. An
ontology with no named individuals needs no extra run. A realization that KM
declines (a dropped clause or an approximate answer) raises a reasoner error.

The object property queries use `km classify --properties`
([`docs/PROPERTIES.md`](../docs/PROPERTIES.md)) in the same way: one one-shot
run per ontology revision, made on the first property query (including the
property axioms of `isEntailed`) or when Protégé asks to precompute
`OBJECT_PROPERTY_HIERARCHY`, cached, dropped on flush, and refused with a
reasoner error when KM declines. Class and individual queries never start it.
An ontology with no object property needs no run. The run can cost much more
than a plain classification (docs/PROPERTIES.md, "Cost"). Protégé's default
preferences show inferred object property information (unsatisfiable, super,
equivalent and inverse properties), and Protégé maps these to
`OBJECT_PROPERTY_HIERARCHY` when you start the reasoner, so with the default
preferences "Start reasoner" should make this run (read from Protégé's
preference mapping, not yet seen in a running Protégé). Turn those displays off in
"Configure reasoner" or mark `OBJECT_PROPERTY_HIERARCHY` as disallowed to skip
it.

Behaviour as HermiT (Protégé integration):

- The constructor does no native work. The first query or
  `precomputeInferences` classifies the ontology as it is then. A run that
  fails (KM refuses the ontology, or the process fails) is remembered for that
  version of the ontology: later calls rethrow the stored exception without a
  new KM run, until the ontology changes or `flush()` runs. The same holds for
  a failed realization or property run. An interrupt or a time out is not
  remembered; the next call starts a new run.
- Queries on an inconsistent ontology throw `InconsistentOntologyException`,
  which Protégé catches to open its inconsistency explanation. Only
  `isConsistent` does not throw. `getTopClassNode`, `getBottomClassNode`,
  `getUnsatisfiableClasses` and the top and bottom property nodes throw as
  well: HermiT 1.4.3.456 does (parity baseline, ontology `ore_ont_5014`).
  `getInstances` throws only when the ontology has individuals.
- Native work reports to the progress monitor of the reasoner configuration
  (started, busy, stopped), ends with `TimeOutException` after `getTimeOut()`
  milliseconds, and ends with `ReasonerInterruptedException` when `interrupt()`
  is called (the one exception Protégé catches). `interrupt()` while idle does
  nothing.
- A named class or object property outside the signature sits between Top and
  Bottom (HermiT's default `FreshEntityPolicy.ALLOW`).
- `isSatisfiable` of an anonymous class expression throws
  `ClassExpressionNotInProfileException` instead of answering `true`.
- `isEntailed(Set)` ignores annotation and declaration axioms.
- `isPrecomputed` is true only for the types the plugin holds now.
- A query the plugin cannot answer soundly and completely throws; it never
  returns an empty or partial answer. The exception is
  `UnsupportedOperationException` (for `isEntailed`:
  `UnsupportedEntailmentTypeException`, and `isEntailmentCheckingSupported`
  agrees with it; for `isSatisfiable` of an expression:
  `ClassExpressionNotInProfileException`). The list is under "Queries that
  throw".
- `owl:Nothing` and `owl:Thing` follow HermiT's hierarchy: the bottom node
  holds `owl:Nothing` and the unsatisfiable classes and is a strict subclass
  of every other node. A leaf class has the bottom node as its only direct
  subclass, `getSubClasses(owl:Thing, true)` lists it only when no other class
  exists, and `getSuperClasses(owl:Nothing, false)` is every other class
  (direct: the leaves). Data and object property hierarchies use the same
  shape with the top and bottom properties.
- `getTimeOut`, `getIndividualNodeSetPolicy` and `getFreshEntityPolicy` return
  what the configuration says (as HermiT does with an `OWLReasonerConfiguration`;
  `Long.MAX_VALUE` when none was set).

Differences from HermiT:

- The individual node set policy of the configuration decides the nodes of
  `getInstances`: `BY_NAME` (the default, as in HermiT) gives one node per
  individual, `BY_SAME_AS` one node per same-individual group.
  `getSameIndividuals` always returns the whole group, as HermiT does.
- A class declared equivalent to `owl:Thing` is a type of every individual,
  but KM's class hierarchy does not yet put it in the node of `owl:Thing`, so
  the node shapes (and the `direct` answers for such individuals) differ.
- HermiT keeps `ObjectInverseOf(r)` out of its property hierarchy when the
  ontology uses no inverse role, and answers such a query with a node of its
  own between top and bottom. The plugin does the same, deciding "uses an
  inverse role" from the axioms in the way HermiT's normalisation does
  (`ObjectInverseOf`, inverse, inverse functional, symmetric and asymmetric
  properties); a case where the two disagree gives one more or one fewer
  inverse expression in the nodes.
- `getObjectPropertyDomains` and `getObjectPropertyRanges` of
  `owl:bottomObjectProperty`: HermiT answers `owl:Thing` (direct) and nothing
  (not direct); KM answers every class (direct: `owl:Nothing`), as for any empty
  property.
- `isEntailed` for property axioms is answered from the semantics. HermiT looks
  an inverse expression up in its hierarchy, so without inverse roles in the
  ontology it fails (null pointer) or answers false for such an axiom, even for
  an empty property; KM answers true. For a property outside the signature, KM
  finds only the trivial entailments; HermiT also finds `p ⊑ p⁻` when every
  model of the ontology has one individual.
- `getDataPropertyDomains(owl:bottomDataProperty)`: HermiT answers
  `owl:Thing`; the bottom property has no pair, so every class is a domain
  (direct: `owl:Nothing`) and KM answers that, as for the bottom object
  property.
- `getDisjointObjectProperties` and `getDisjointDataProperties` of an empty
  property other than the bottom property: HermiT leaves out the top property,
  which is disjoint with an empty property. KM lists every node, as HermiT
  does for the bottom property itself.
- `ObjectPropertyDomain` and `ObjectPropertyRange` with a class expression are
  not answered by `isEntailed` (`UnsupportedEntailmentTypeException`).

## Queries that throw

These calls throw `UnsupportedOperationException` (the engine work items):

- `getObjectPropertyValues`, `getDataPropertyValues`, `getDifferentIndividuals`;
- `getDisjointClasses` of a satisfiable class other than `owl:Thing`,
  `getDisjointObjectProperties` and `getDisjointDataProperties` of a
  satisfiable property;
- `getSuperClasses`, `getSubClasses`, `getEquivalentClasses`,
  `getDisjointClasses` and `getInstances` with an anonymous class expression
  (a conjunction, restriction, complement, enumeration, and so on);
- the data property methods listed above, for an ontology outside their
  fragment (a data property in a class axiom, a disjointness or key, a complex
  range, domains or ranges that cannot be combined);
- `isSatisfiable` of an anonymous class expression
  (`ClassExpressionNotInProfileException`);
- `isEntailed` of an axiom type outside the table above, or with a class
  expression or an anonymous individual where the table says "named"
  (`UnsupportedEntailmentTypeException`).

`precomputeInferences` ignores a type it does not compute, as the OWL API
specifies.

## Install in Protégé

### From "Check for plugins"

Once the plugin is listed in the Protégé plugin registry:

1. Start Protégé and choose **File → Check for plugins...**.
2. Tick **Kobayashi-MaRust Reasoner** and click **Install**.
3. Restart Protégé.
4. Open an ontology and choose **Reasoner → Kobayashi-MaRust → Start
   reasoner**.

Protégé 5 and Protégé 6 read separate lists, and each list points at the jar
built for that line.

### By hand

1. Download `kobayashi-marust-protege5-<version>.jar` (Protégé 5.6) or
   `kobayashi-marust-protege6-<version>.jar` (Protégé 6) from the
   [releases](https://github.com/bio-ontology-research-group/kobayashi-marust/releases).
2. Copy it into the `plugins` directory inside the Protégé installation and
   remove any older `kobayashi-marust-protege*.jar` there.
3. Restart Protégé.
4. Open an ontology and choose **Reasoner → Kobayashi-MaRust → Start
   reasoner**.
5. On a supported inferred named-class `SubClassOf` row, click the purple
   **Explain inference** (`?`) button. If a service chooser appears, select
   **Kobayashi-MaRust native source justifications**.

The `plugins` directory is beside the Protégé launcher in the platform
independent distribution. Typical locations are:

- Linux: `/opt/Protege-5.6.x/plugins/`
- macOS application bundle:
  `/Applications/Protege.app/Contents/Java/plugins/`
- Windows: `C:\Program Files\Protege-5.6.x\plugins\`

The exact directory may differ if Protégé was unpacked elsewhere. Use the
`plugins` directory belonging to the launcher you actually start.

### The bundled km executable

The release jars contain `km` for five platforms under
`native/<os>-<arch>/` (`linux-x86_64`, `linux-aarch64`, `macos-x86_64`,
`macos-aarch64`, `windows-x86_64`) with their SHA-256 sums in
`native/SHA256SUMS`. On first use the plugin unpacks the executable for the
running platform into a per-user cache and checks its sum:

- Linux: `$XDG_CACHE_HOME/kobayashi-marust/protege/` or
  `~/.cache/kobayashi-marust/protege/`
- macOS: `~/Library/Caches/kobayashi-marust/protege/`
- Windows: `%LOCALAPPDATA%\kobayashi-marust\protege\`

Each plugin version and executable gets its own subdirectory, so you can
delete old ones at any time.

### Use another km executable

The plugin looks for `km` in this order:

1. the Java property `km.bin`;
2. the environment variable `KM_BIN`;
3. the bundled executable for the running platform;
4. `km` (`km.exe` on Windows) on `PATH`.

If none fits, starting the reasoner fails with a message that names the
platform. Set `km.bin` or `KM_BIN` to use your own build, for example on a
platform the jar does not cover:

```sh
export KM_BIN=/absolute/path/to/km
./run.sh
```

On macOS, applications launched from Finder may not inherit shell environment
variables. Add the following JVM option to Protégé's launcher configuration:

```text
-Dkm.bin=/absolute/path/to/km
```

The same JVM property works in the Linux and Windows launcher configuration.
Use an absolute path. On Windows, point it to `km.exe`.

Classification defaults to a 600 second subprocess timeout. Override it with
`KM_TIMEOUT_SECONDS` or the JVM property `km.timeout.seconds`.

## Build KM and the plugin

Build the release reasoner from the repository root:

```sh
cd engine
cargo build --release --bin km
```

Build and test the Protégé 5 jar, then the Protégé 6 jar:

```sh
cd ../protege
mvn verify -Dkm.bin=/absolute/path/to/km
mvn -Pprotege6 verify -Dkm.bin=/absolute/path/to/km
```

The tests need a `km` executable: pass `-Dkm.bin`, or build `km` under the
checkout-local `.work/target`. The jars are:

```text
protege/target/protege5/kobayashi-marust-protege5-1.6.4.jar
protege/target/protege6/kobayashi-marust-protege6-1.6.4.jar
```

A developer build bundles no `km`. To bundle executables, lay them out as
`<dir>/<os>-<arch>/km` (`km.exe` for `windows-x86_64`) and pass the
directory:

```sh
mvn verify -Dkm.native.dir=/absolute/path/to/native
```

The verify phase checks each bundled executable against `native/SHA256SUMS`.
Add `-Dkm.native.require=all` to fail unless all five release platforms are
present, as the release workflow does. The workflow
[`.github/workflows/protege-plugin.yml`](../.github/workflows/protege-plugin.yml)
builds `km` on native GitHub runners for the five platforms, builds and tests
both jars with all five executables, installs them in stock Protégé 5.6.9 and
6.0.0-alpha-1, and attaches them to the release of a `v*` tag.

### Use the OWLAPI explanation adapter

Java clients can construct the factory directly or discover it with
`ServiceLoader`:

```java
ExplanationGenerator<OWLAxiom> generator =
    new KMExplanationGeneratorFactory()
        .createExplanationGenerator(ontology);
Set<Explanation<OWLAxiom>> explanations =
    generator.getExplanations(entailment, 2);
```

The adapter reads the same `km.bin` and timeout settings. Explanation-specific
bounds use `km.explain.max.axioms`, `km.explain.max.checks`,
`km.explain.max.source.bytes`, and `km.explain.all.justifications.cap`, with
corresponding upper-case environment variables documented in
[`docs/EXPLANATIONS.md`](../docs/EXPLANATIONS.md).

The bundle registers a service for Protégé 5.6's standard core Explain action.
Its panel lets the user select the maximum number of source justifications,
generate them asynchronously, cancel a native run, and see whether the result
is a complete enumeration or a bounded prefix. Every displayed support has
passed KM's final-subset reclassification and subset-minimality checks.

The supported OWLAPI and GUI surface is deliberately exact: a query must be an
`OWLSubClassOfAxiom` with a named subclass and named superclass. Named-class
unsatisfiability and ontology inconsistency use `owl:Nothing` as documented.
Property entailments, individual assertions, and anonymous class expressions
throw `UnsupportedEntailmentException`; they do not return an empty set.

The separate upstream Explanation Workbench has no custom-factory extension
point and may still use its own generic reasoner-backed generator. KM's native
panel integrates with Protégé's core Explain action instead of claiming a
Workbench registration.

## Runtime behavior

The plugin:

1. Flattens the active ontology's loaded imports closure.
2. Serializes the merged axioms to a temporary OWL functional-syntax document.
3. Runs `km classify --lines --format functional`.
4. Maps results back into the OWL API using complete entity IRIs.

Flattening imports avoids silently classifying only the root ontology. Protégé
must have successfully loaded every import before reasoning starts; the plugin
rejects an unresolved import.

KM runs outside the Protégé JVM, so its native memory is separate from the Java
heap. Errors, timeouts, and any result that reports dropped clauses are
reported as reasoner failures in Protégé rather than displayed as a partial
classification.
Incremental-session and explanation cancellation, timeout, and disposal stop
the complete native process tree and wait for route workers to exit. They do
not leave an orphaned worker consuming memory after the OWLAPI call returns.
A declined buffered transaction leaves the last committed hierarchy queryable.
After the caller removes or corrects the unsupported change, the next
`flush()` starts a clean native session and commits the complete current
imports closure.

## Test coverage

The headless OWL API tests cover:

- disjunctive subsumption;
- the bundled kinship ontology;
- inclusion of the loaded imports closure; and
- rejection of unresolved imports;
- distinct classes that share the same local-name fragment;
- individual queries (`IndividualsTest`): types, instances, same individuals,
  entailment, lazy realization and its invalidation after a change; and
- the same queries compared with HermiT on a small ABox, a nominal and
  cardinality ontology, and the W3C wine and food ontologies
  (`HermitDifferentialTest`; HermiT is a test-scope dependency).

The explanation tests cover exhaustive and bounded multiple EL
justifications, named unsatisfiability, CB inverse-role inference, rules/HT
inconsistency, explicit rejection of anonymous/property/individual queries,
fail-closed source bounds, and `ServiceLoader` discovery. Headless controller
tests cover completion metadata and cancellation. Native CLI tests separately
assert EL, CB, and HT mechanism provenance and rejection of a forced route.

Unit tests cover how the plugin finds `km`: the resolution order, unpacking
and reusing the bundled executable, replacing a corrupt cache entry, a
checksum mismatch, and platform naming. All tests run against both the
Protégé 5 and the Protégé 6 build.

The Maven `verify` phase also unpacks the OSGi JAR and fails unless the native
explanation service, result panel, `plugin.xml`, Java service metadata, and
pinned embedded dependencies are present.

### Test the packaged plugin in a real Protégé installation

Maven's dependency classpath does not reproduce OSGi package resolution. Run
the installation smoke test against an unpacked stock Protégé 5.6.x or
Protégé 6 distribution before releasing:

```sh
protege/run-installation-smoke.sh \
  /absolute/path/to/Protege-5.6.9 \
  "$PWD/protege/target/protege5/kobayashi-marust-protege5-1.6.4.jar"

protege/run-installation-smoke.sh \
  /absolute/path/to/Protege-6.0.0-alpha-1 \
  "$PWD/protege/target/protege6/kobayashi-marust-protege6-1.6.4.jar"
```

Without a third argument the jar must bundle `km` for the running platform:
the script unsets `KM_BIN`, removes every `km` from `PATH`, and checks that
the plugin unpacked and ran the bundled executable. With a third argument,
`KM_BIN` points at that executable and the script checks that nothing was
unpacked. Set `KM_SMOKE_WORK_DIR` to choose where the run keeps its files
(default `.work`).

The script installs the packaged plugin and a separate one-shot consumer
bundle into that distribution. Through Protégé's Felix container, the consumer
requires the KM bundle to be active, classifies a small ontology, applies a
non-buffering OWLAPI addition through the retained native session, and obtains
the exact source-axiom justification through the bundle's OWL Explanation API.
The consumer bundle is test-only and is never included in the released plugin.

The smoke launcher uses Java headless mode so it can run in CI. Protégé's own
Swing application activator consequently reports `HeadlessException`; the
test does not treat that expected GUI-only error as a plugin failure. It does
fail on any KM resolution/start error, native reasoning failure, incorrect
incremental answer, or incorrect explanation.
