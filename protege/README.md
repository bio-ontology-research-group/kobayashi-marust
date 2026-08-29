# Kobayashi-MaRust Protégé plugin

This module provides a Protégé Desktop reasoner plugin for KM. It appears in
the **Reasoner** menu as **Kobayashi-MaRust** and supplies the inferred named
class hierarchy, equivalence classes, unsatisfiable classes, and ontology
consistency.

The plugin is a TBox classifier. Property hierarchy, property assertion, and
individual realization queries are not currently exposed through the OWL API.
The 0.3.0 bundle also contains an OWL Explanation API 2.0.1
`ExplanationGenerator` and `ExplanationGeneratorFactory`. It returns verified,
source-axiom justifications for named-class entailments through KM's native
schema-2 protocol. See
[`docs/EXPLANATIONS.md`](../docs/EXPLANATIONS.md) for supported entailments,
bounds, and the Protégé explanation panel.

## Requirements

- Protégé Desktop 5.6.x. The plugin is compiled against the Maven-published
  Protégé 5.6.6 API and is intended for the current Protégé 5.6 line.
- Java 11 or newer.
- The native `km` executable for the user's operating system and architecture.
  Python and `moose` are not required.

The build pins OWLAPI 4.5.29, OWL Explanation 2.0.1, its telemetry 2.0.0
runtime, Protégé 5.6.6, and Gson 2.11.0. Protégé and OWLAPI packages are
provided by the host application; the bundle embeds the explanation runtime
dependencies and Gson.
The embedded OWL Explanation and telemetry JARs remain intact with their
upstream LGPL 3 license metadata; KM's own code remains BSD-3-Clause.

## Build KM and the plugin

Build the release reasoner from the repository root:

```sh
cd engine
cargo build --release --bin km
```

Build and test the plugin:

```sh
cd ../protege
mvn test
mvn package
```

The OSGi plugin bundle is:

```text
protege/target/kobayashi-marust-protege-0.3.0.jar
```

Set `KM_BIN` while testing if `km` is not on `PATH`:

```sh
KM_BIN=/absolute/path/to/km mvn test
```

## Install in Protégé

1. Download and unpack Protégé Desktop 5.6.x from the
   [Protégé website](https://protege.stanford.edu/software/).
2. Copy `kobayashi-marust-protege-0.3.0.jar` into the `plugins` directory
   inside the Protégé installation.
3. Put the `km` executable on the process `PATH`, or configure its absolute
   path as described below.
4. Restart Protégé.
5. Open an ontology and choose **Reasoner → Kobayashi-MaRust → Start
   reasoner**.
6. On a supported inferred named-class `SubClassOf` row, click the purple
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

### Configure the KM executable

The plugin first reads the Java property `km.bin`, then the environment
variable `KM_BIN`, and finally tries `km` on `PATH`.

The environment variable is usually the simplest installation:

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
- distinct classes that share the same local-name fragment.

The explanation tests cover exhaustive and bounded multiple EL
justifications, named unsatisfiability, CB inverse-role inference, rules/HT
inconsistency, explicit rejection of anonymous/property/individual queries,
fail-closed source bounds, and `ServiceLoader` discovery. Headless controller
tests cover completion metadata and cancellation. Native CLI tests separately
assert EL, CB, and HT mechanism provenance and rejection of a forced route.

The Maven `verify` phase also unpacks the OSGi JAR and fails unless the native
explanation service, result panel, `plugin.xml`, Java service metadata, and
pinned embedded dependencies are present.

### Test the packaged plugin in a real Protégé installation

Maven's dependency classpath does not reproduce OSGi package resolution. Run
the installation smoke test against an unpacked stock Protégé 5.6.6
distribution before releasing:

```sh
protege/run-installation-smoke.sh \
  /absolute/path/to/Protege-5.6.6 \
  "$PWD/protege/target/kobayashi-marust-protege-0.3.0.jar" \
  "$PWD/.work/target/release/km"
```

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
