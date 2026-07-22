# Kobayashi-MaRust Protégé plugin

This module provides a Protégé Desktop reasoner plugin for KM. It appears in
the **Reasoner** menu as **Kobayashi-MaRust** and supplies the inferred named
class hierarchy, equivalence classes, unsatisfiable classes, and ontology
consistency.

The plugin is a TBox classifier. Property hierarchy, property assertion, and
individual realization queries are not currently exposed through the OWL API.
The native binary also provides a bounded, versioned source-axiom explanation
protocol. The current plugin does not display it yet; see
[`docs/EXPLANATIONS.md`](../docs/EXPLANATIONS.md) for the integration contract.

## Requirements

- Protégé Desktop 5.6.x. The plugin is compiled against the Maven-published
  Protégé 5.6.6 API and is intended for the current Protégé 5.6 line.
- Java 11 or newer.
- The native `km` executable for the user's operating system and architecture.
  Python and `moose` are not required.

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
protege/target/kobayashi-marust-protege-0.2.0.jar
```

Set `KM_BIN` while testing if `km` is not on `PATH`:

```sh
KM_BIN=/absolute/path/to/km mvn test
```

## Install in Protégé

1. Download and unpack Protégé Desktop 5.6.x from the
   [Protégé website](https://protege.stanford.edu/software/).
2. Copy `kobayashi-marust-protege-0.2.0.jar` into the `plugins` directory
   inside the Protégé installation.
3. Put the `km` executable on the process `PATH`, or configure its absolute
   path as described below.
4. Restart Protégé.
5. Open an ontology and choose **Reasoner → Kobayashi-MaRust → Start
   reasoner**.

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

## Test coverage

The headless OWL API tests cover:

- disjunctive subsumption;
- the bundled kinship ontology;
- inclusion of the loaded imports closure; and
- rejection of unresolved imports;
- distinct classes that share the same local-name fragment.

The Maven bundle build also checks that the plugin classes and `plugin.xml` are
packaged into a valid OSGi JAR.
