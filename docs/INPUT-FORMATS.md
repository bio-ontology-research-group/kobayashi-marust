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

## Dependencies and licensing

The adapter uses Horned-OWL 1.4 with remote resolution disabled. Horned-OWL is
LGPL-3.0 licensed; KM's own source remains BSD-3-Clause. Distribution must
preserve the applicable Horned-OWL license notices and relinking/source rights.
