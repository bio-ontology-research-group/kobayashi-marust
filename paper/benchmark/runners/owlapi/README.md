# Common OWLAPI baseline runner

`FullIriClassifier` is compiled separately with each reasoner's pinned OWLAPI
dependency graph. It accepts the factory class, ontology path, and output path.
The output contract is intentionally independent of OWLAPI renderers:

- `C<TAB>true|false|unknown`: consistency, with `unknown` reserved for a
  baseline that does not implement this service;
- `U<TAB>iri`: a named unsatisfiable class;
- `S<TAB>sub-iri<TAB>super-iri`: a strict named subsumption;
- `M<TAB>key<TAB>value`: metadata; and
- `Z<TAB>complete`: mandatory final sentinel.

The runner writes to `<output>.part` and renames only after classification,
serialization, and disposal complete. The benchmark harness must reject files
without exactly one consistency row, one terminal sentinel, sorted unique `U`
and `S` rows, and metadata counts matching the parsed records.

Factory classes for the frozen baseline set are:

| Reasoner | Factory class |
|---|---|
| HermiT | `org.semanticweb.HermiT.ReasonerFactory` |
| JFact | `uk.ac.manchester.cs.jfact.JFactFactory` |
| Openllet | `openllet.owlapi.OpenlletReasonerFactory` |
| ELK | `org.semanticweb.elk.owlapi.ElkReasonerFactory` |
| Whelk | `org.geneontology.whelk.owlapi.WhelkOWLReasonerFactory` |
| MORe | `org.semanticweb.more.reasoner.MOReReasonerFactory` |

MORe is compiled in its own OWLAPI 3.4.10 source environment. If its API is
not source-compatible with this runner, keep an OWLAPI-3 adapter with the same
wire contract rather than changing MORe's dependency graph.

The frozen Java invocation includes
`--add-opens=java.base/java.lang=ALL-UNNAMED`. JFact 5.0.3 transitively uses an
older Guice release that otherwise fails during OWLAPI manager construction on
modular JVMs. The flag is applied to every Java baseline so the process command
is uniform; it changes reflective access only, not reasoner configuration.
