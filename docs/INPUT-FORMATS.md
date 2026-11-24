# OWL input formats

KM has one trusted normalization pipeline. Native functional syntax enters it
directly. OWL/XML, RDF/XML, and Turtle are first parsed into Horned-OWL's OWL 2
structural model, serialized as functional syntax, and then passed through the
same KM frontend.

```text
km classify ontology.ofn
km classify ontology.owx
km classify ontology.owl
km classify ontology.ttl
km classify --format rdfxml ontology.data
```

The `profile` and `features` commands accept the same formats and
`--format` option.

## Safety contract

- Format detection uses content first and the extension second.
- RDF input uses strict parsing and must map completely to OWL structures.
  Remaining triples, disconnected blank-node structures, class expressions,
  property expressions, data ranges, rules, or annotations cause an honest
  unsupported result.
- All accepted formats subsequently use KM's existing IRI typing,
  normalization, source profile, route selection, and clause generation.
- `owl:imports` is rejected. KM does not perform network access or silently
  classify only the importing document. Merge the import closure into one
  self-contained ontology before classification.
- Manchester syntax is not accepted by this interface yet. Horned-OWL 1.4's
  published feature list mentions Manchester syntax, but its current crate
  source does not expose a Manchester parser module.

## Entity names in output

By default (`--iris source`) `km classify` prints every entity as the input
spells it. A Functional-Syntax input with `Prefix(ex:=<http://example.org/>)`
gives `SUB ex:A ex:B`; a full IRI is printed without angle brackets; an entity
written in more than one spelling is printed as its full IRI
([REALIZATION.md](REALIZATION.md)). OWL/XML, RDF/XML and Turtle inputs are
converted without prefixes, so their names are full IRIs.

`km classify --iris full` (or `KM_IRIS=full`) prints every entity name as its
full IRI, for every input syntax and in every output: the JSON object,
`--json-edges`, and every `--lines` row, including those of `--realize`,
`--values`, `--different`, `--properties`, `--data-properties` and `--top`.
Names are expanded with the input's own `Prefix` declarations (the empty
prefix `:` included) and the standard `owl`, `rdf`, `rdfs` and `xsd`
prefixes, so `owl:Thing` becomes `http://www.w3.org/2002/07/owl#Thing`. A
name that is already a full IRI, an anonymous individual (`_:b`) and a name
with an undeclared prefix stay as they are; `ObjectInverseOf(r)` keeps its
form with `r` expanded. After expansion each list is sorted again, and the
unordered `SAME` and `DIFFERENT` pairs are put in order, so the same ontology
gives the same bytes in any syntax. Literals and the `APPROXIMATE` and
`LENIENT` texts are not changed. One ambiguity remains: a full IRI written
without a `//` authority (`urn:x`) whose scheme is also a declared prefix
name (`Prefix(urn:=<...>)`) is read as a prefixed name. `km explain` quotes
source axioms as written, together with the document's prefix declarations,
and has no such option.

## Dependencies and licensing

The adapter uses Horned-OWL 1.4 with remote resolution disabled. Horned-OWL is
LGPL-3.0 licensed; KM's own source remains BSD-3-Clause. Distribution must
preserve the applicable Horned-OWL license notices and relinking/source rights.
