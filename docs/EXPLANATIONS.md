# Source-axiom explanations

KM has an opt-in, bounded command for extracting one source-level
justification for a named-class inference. It is intended as the protocol
boundary for command-line tools and a later OWLAPI or Protégé explanation UI.
The current Protégé plugin does not yet display explanations.

## Supported queries

The input must be a self-contained OWL functional-syntax document. Imports
must already be flattened, as they are for normal Protégé classification.
The first release supports:

- a named-class subsumption `A ⊑ B`;
- named-class unsatisfiability `A ⊑ owl:Nothing`; and
- ontology inconsistency.

Use complete IRIs so an OWLAPI caller can map every result without local-name
collisions:

```sh
km explain ontology.ofn subclass \
  http://example.org/A http://example.org/C

km explain --pretty ontology.ofn unsatisfiable http://example.org/A

km explain ontology.ofn inconsistent
```

`--route NAME` uses the same named route contract as `km classify`. The
default is `auto`. The safety bounds are:

- `--max-axioms N`, default 256;
- `--max-checks N`, default `max-axioms + 1`, including the initial full-source
  check; and
- `--max-source-bytes N`, default 8 MiB.

The command exits 3 when the input is outside this scope or a bound prevents
the initial check. It exits 1 if a classification check fails. It never turns
an error or resource decline into an explanation.

## JSON protocol

Standard output is one compact JSON object. `--pretty` changes whitespace
only. The versioned fields are designed to be consumed without a Rust-specific
library:

```json
{
  "schemaVersion": 1,
  "status": "entailed",
  "query": {
    "type": "sub-class",
    "subClass": "http://example.org/A",
    "superClass": "http://example.org/C"
  },
  "method": "black-box-source-axiom-deletion",
  "requestedRoute": "auto",
  "reasonerVersion": "0.1.0",
  "sourceAxiomCount": 3,
  "classificationChecks": 4,
  "oracleSubsetMinimal": true,
  "limitReached": false,
  "justifications": [
    {
      "axiomCount": 2,
      "axioms": [
        {
          "id": "ax000001",
          "ordinal": 1,
          "functionalSyntax": "SubClassOf(<http://example.org/A> <http://example.org/B>)"
        },
        {
          "id": "ax000002",
          "ordinal": 2,
          "functionalSyntax": "SubClassOf(<http://example.org/B> <http://example.org/C>)"
        }
      ]
    }
  ],
  "notes": ["..."]
}
```

`status` is `not-entailed` and `justifications` is empty when the full source
does not produce the requested entailment. A source axiom ID is its one-based
position among children of `Ontology(...)`, zero-padded for lexical sorting.
`functionalSyntax` is a canonical spelling of that source node, including its
axiom annotations. An OWLAPI bridge can parse this spelling or use `ordinal` to
map the result back to the exact axiom in the flattened document.

## Method and guarantees

The extractor first confirms the query against the complete source. It then
deletes one source axiom at a time and retains the deletion only after KM still
entails the query. OWL entailment is monotone, so one completed deletion pass
is subset-minimal: removing any one remaining source axiom makes the KM oracle
stop reporting the query.

If `--max-checks` ends the pass early, the last revalidated set is still an
entailing source set. The report sets `limitReached: true` and
`oracleSubsetMinimal: false`; it does not claim minimality.

This is an oracle-based justification, not an independently checked proof
object and not a trace of individual CB, EL, or hypertableau rule applications.
Its soundness depends on the selected KM classification route. The method does
not find every justification, a minimum-cardinality justification, or an
explanation for property and individual inferences. `oracleSubsetMinimal`
means minimal relative to source axiom occurrences and the selected KM route,
not minimal under arbitrary OWL axiom rewriting.

The extractor rebuilds each candidate ontology from source functional syntax.
It therefore explains generated definer and normalized-clause inferences in
terms of their source OWL axioms rather than exposing internal `Q_*`, `f_*`, or
bridge symbols.

## Performance and calculus certification

Explanation mode can require `N + 1` complete classifications for `N` source
axioms. It is intentionally bounded and disabled during normal classification.
When `km explain` is not invoked, the implementation allocates no provenance
map, adds no clause fields, and performs no explanation checks.

This feature does not change what the CB calculus derives. It only invokes the
existing classifier on source subsets, so it introduces no Lean
re-certification obligation. A future inference-level proof trace inside the
CB engine would need a separate review of proof reconstruction, and any change
to rule applicability would still require the normal calculus re-certification.

## OWLAPI and Protégé integration path

An OWLAPI caller can use the same flow as the existing KM classifier bridge:

1. flatten the loaded imports closure;
2. save it as OWL functional syntax;
3. execute `km explain` with complete class IRIs;
4. parse schema version 1; and
5. parse each returned `functionalSyntax` axiom or map its source ordinal back
   to the flattened ontology.

Keeping extraction in the native process avoids coupling the JSON contract to
a particular OWLAPI or Protégé release. A GUI integration should show the
`oracleSubsetMinimal` and `limitReached` fields rather than labeling every
bounded result as minimal.
