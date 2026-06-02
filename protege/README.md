# Kobayashi-MaRust — Protege plugin

A [Protege](https://protege.stanford.edu/) **reasoner plugin** that classifies the
active ontology with the Kobayashi-MaRust SROIQ / OWL 2 DL context reasoner.
It appears in Protege's *Reasoner* menu as **Kobayashi-MaRust**; "Start reasoner"
then computes the inferred class hierarchy and unsatisfiable classes.

## How it works

The plugin is a thin Java `OWLReasoner` (`KMReasoner`) over the OWL API. On
classification it:

1. serialises the active ontology to OWL functional syntax,
2. runs the bridge `engine/py/owl_classify.py`, which performs the **real**
   normalisation (moose's `normalise` + `augment`) and runs the Rust engine,
3. parses the named-class subsumptions and unsatisfiable classes back into an
   OWL API class hierarchy (with equivalence grouping and direct/indirect
   sub-/super-class queries).

It is a **TBox classifier**: class hierarchy + (un)satisfiability. Property and
individual inferences are intentionally empty.

## Runtime requirements

Because normalisation is shared with `moose`, the plugin shells out to Python:

- Python 3 with the `moose` package importable (set `MOOSE_HOME`), and
- the built `kobayashi-marust` engine binary (`cargo build --release` in
  `../engine`).

These are located via system properties (or environment variables), all
optional with sensible defaults:

| property      | env           | default                                   |
|---------------|---------------|-------------------------------------------|
| `km.home`     | `KM_HOME`     | `user.dir` (point at the repo root)       |
| `km.python`   | `KM_PYTHON`   | `python3`                                 |
| `km.classify` | `KM_CLASSIFY` | `<km.home>/engine/py/owl_classify.py`     |
| `km.engine`   | `KM_ENGINE`   | autodetected under `engine/target/release`|

In Protege, set these in the launch script (e.g. `-Dkm.home=/path/to/kobayashi-marust`).

## Build

```sh
mvn -DskipTests package      # -> target/kobayashi-marust-protege-0.1.0.jar (OSGi bundle)
```

Drop the jar into Protege's `plugins/` directory and restart Protege.

## Test (headless, no GUI)

```sh
mvn test                     # drives KMReasoner via the OWL API
```

The tests need Python + moose + the engine binary (as above); `km.home`
defaults to the repository root. They check:

- disjunctive subsumption `A ⊑ B⊔C, B⊑D, C⊑D ⊢ A ⊑ D`, and
- the bundled `examples/ontologies/kinship.ofn` (e.g. `Father ⊑ Person, Parent,
  Male, Narcissist`), matching the HermiT oracle.
