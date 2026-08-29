# Source-axiom explanations

KM can extract bounded, source-level justifications for named-class
entailments. The native command has a versioned JSON contract, and the
Protégé module implements the standard OWL Explanation API
`ExplanationGenerator<OWLAxiom>` and `ExplanationGeneratorFactory<OWLAxiom>`.
Explanation work is opt-in and adds no provenance state to normal
classification.

## Supported entailments

`km explain` accepts a self-contained OWL functional-syntax document and one
of these queries:

- named-class subsumption `A SubClassOf B`;
- named-class unsatisfiability `A SubClassOf owl:Nothing`; or
- ontology inconsistency.

The named-class OWLAPI entailment surface also applies the standard OWL
boundary cases: reflexive subclass queries, `owl:Nothing SubClassOf A`, and
`A SubClassOf owl:Thing` are tautologies; an unsatisfiable named subclass
entails every named superclass; and an inconsistent ontology entails every
supported named-class query. A tautology has one verified empty source-axiom
justification. `KMReasoner` and the explanation generator use the same
semantics for these cases.

Use complete IRIs. Prefix declarations in the source are resolved by exact
IRI expansion, never by local-name matching.

```sh
km explain ontology.ofn subclass \
  http://example.org/A http://example.org/C

km explain --pretty ontology.ofn \
  unsatisfiable http://example.org/A

km explain ontology.ofn inconsistent
```

Property entailments, assertions about individuals, anonymous class
expressions, and general OWL axioms are not yet explanation queries. Imports
must already be loaded and flattened. The OWLAPI adapter does this flattening
and rejects unresolved imports.

## Safety boundary and mechanisms

Every oracle call uses `--route auto`, including every axiom-deletion
candidate. `manual`, all named matrix procedures, and ambient `KM_ROUTE`
settings are rejected or overridden. A forced mechanism cannot escape the
source-profile gate.

The contract is mechanism-independent. Depending on the candidate source,
the production gate may use:

- exact EL++ completion for an EL-safe candidate;
- the sound-and-complete CB procedure on its admitted SRIQ core fragment; or
- a validated complete-answer-or-defer HT mechanism admitted by the gate.

The regression suite explicitly exercises EL completion, CB inverse-role
reasoning, ordinary HT over a 6,001-axiom sparse-support source, qualified
cardinality pigeonhole reasoning, the certified native nominal/ABox route, and
the validated DL-safe-rules HT consistency mechanism. A source deletion may
change the profile and therefore the selected implementation. That is safe
because minimisation asks the same monotonic OWL entailment of each source
subset and each subset re-enters the production gate.

The rules HT stage can certify complete-source consistency even when its
subsequent taxonomy-only fall-through reports dropped clauses. That internal
certificate is accepted only for an inconsistency query. Subsumption and
named-unsatisfiability queries still reject any dropped clause. All other
route declines, dropped clauses, worker errors, and malformed results stop the
extraction instead of being interpreted as non-entailment.

## Multiple justifications and bounds

KM first checks the full source and minimises one entailing subset. Sources of
up to 32 axioms use deterministic one-axiom deletion. Larger sources use
monotone delta debugging: entailing chunks are removed first and partition
granularity increases to singleton deletions only around the surviving
support. This preserves subset minimality while avoiding one complete
classification per source axiom when a large ontology has a sparse support.
KM reclassifies the exact final subset before publishing it. A deterministic
hitting-set tree then excludes each axiom of a found support to search for
alternatives. Every returned support has both `verified: true` and
`subsetMinimal: true`.

The bounds are:

- `--max-axioms N`, default 256;
- `--max-source-bytes N`, default 8 MiB;
- `--max-justifications N`, default 1; and
- `--max-checks N`, counting every complete classification. When omitted,
  the CLI uses `(max-axioms + 2) * max-justifications`.

If the check budget expires during minimisation, that unfinished candidate is
discarded. Previously completed and independently revalidated supports remain
valid, but the report marks the enumeration incomplete. The OWLAPI adapter is
stricter and throws `ExplanationException` on check-budget exhaustion.

`enumerationComplete: true` means the hitting-set queue was exhausted and all
source-occurrence-minimal supports were found. `justificationLimitReached:
true` means the requested count was reached without proving that no further
support exists. These are subset-minimal explanations, not necessarily
minimum-cardinality explanations.

## JSON protocol, schema 2

Standard output contains one JSON object. `--pretty` changes whitespace only.
A representative response is:

```json
{
  "schemaVersion": 2,
  "status": "entailed",
  "query": {
    "type": "sub-class",
    "subClass": "http://example.org/A",
    "superClass": "http://example.org/C"
  },
  "method": "black-box-hitting-set-source-axiom-deletion",
  "requestedRoute": "auto",
  "reasonerVersion": "0.1.0",
  "sourceAxiomCount": 3,
  "classificationChecks": 5,
  "classificationCheckLimit": 32,
  "justificationLimit": 1,
  "oracleSubsetMinimal": true,
  "enumerationComplete": false,
  "limitReached": true,
  "checkLimitReached": false,
  "justificationLimitReached": true,
  "prefixDeclarations": ["Prefix(:=<http://example.org/>)"],
  "justifications": [
    {
      "axiomCount": 2,
      "verified": true,
      "subsetMinimal": true,
      "axioms": [
        {
          "id": "ax000001",
          "ordinal": 1,
          "functionalSyntax": "SubClassOf(:A :B)"
        },
        {
          "id": "ax000002",
          "ordinal": 2,
          "functionalSyntax": "SubClassOf(:B :C)"
        }
      ]
    }
  ],
  "notes": ["..."]
}
```

`status` is `not-entailed` and `justifications` is empty when the full source
does not entail the query. An axiom ID is based on its one-based position
among children of `Ontology(...)`. `functionalSyntax` retains the complete
source axiom, including axiom annotations. `prefixDeclarations` makes every
returned spelling independently parseable.

The verifier is KM's automatically gated classifier, not an independent proof
checker. The report therefore makes an oracle-relative claim. It does not
turn the portfolio's validation evidence into a proof of the full executable.

## OWLAPI adapter

The `protege` Maven module pins:

- OWLAPI 4.5.29;
- OWL Explanation API 2.0.1;
- its required telemetry runtime 2.0.0;
- Protégé 5.6.6; and
- Gson 2.11.0.

Use the factory directly:

```java
ExplanationGenerator<OWLAxiom> generator =
    new KMExplanationGeneratorFactory()
        .createExplanationGenerator(ontology);

Set<Explanation<OWLAxiom>> firstTwo =
    generator.getExplanations(entailment, 2);
```

The factory snapshots the complete imports closure when it creates a
generator. Later changes to the caller's mutable ontology do not alter an
in-flight enumeration. When a `KMReasoner` is available, bind the generator to
its committed revision rather than passing the mutable root ontology:

```java
ExplanationGenerator<OWLAxiom> committed = reasoner.createExplanationGenerator();
// Equivalent: factory.createExplanationGenerator(reasoner)
```

Buffered pending changes then stay invisible until `flush()`, and a failed
incremental transaction leaves explanations bound to the preceding successful
revision. The factory also provides the corresponding reasoner-plus-progress-
monitor overload for Protégé workbench integration.

The unbounded API overload, `getExplanations(entailment)`, must satisfy the
OWL Explanation API's all-explanations contract. KM searches only up to the
configured safety cap and throws if enumeration is still incomplete. Use the
bounded overload when a finite prefix is acceptable.

The adapter supports named `OWLSubClassOfAxiom` objects. It maps
`A SubClassOf owl:Nothing` to named unsatisfiability and
`owl:Thing SubClassOf owl:Nothing` to ontology inconsistency. Returned
functional-syntax nodes are parsed back into `OWLAxiom` objects and checked
against the flattened source ontology before an `Explanation` is exposed.

`META-INF/services/org.semanticweb.owl.explanation.api.ExplanationGeneratorFactory`
registers `KMExplanationGeneratorFactory` for ordinary Java `ServiceLoader`
clients. Configuration uses a Java property first, then an environment
variable:

| purpose | Java property | environment | default |
|---|---|---|---:|
| native executable | `km.bin` | `KM_BIN` | `km` |
| process timeout | `km.timeout.seconds` | `KM_TIMEOUT_SECONDS` | 600 s |
| source axioms | `km.explain.max.axioms` | `KM_EXPLAIN_MAX_AXIOMS` | 256 |
| checks | `km.explain.max.checks` | `KM_EXPLAIN_MAX_CHECKS` | 4096 |
| source bytes | `km.explain.max.source.bytes` | `KM_EXPLAIN_MAX_SOURCE_BYTES` | 8 MiB |
| all-overload cap | `km.explain.all.justifications.cap` | `KM_EXPLAIN_ALL_JUSTIFICATIONS_CAP` | 8 |

## Protégé GUI

The KM 0.3.0 OSGi bundle contains both the OWLAPI adapter and a native service
for Protégé 5.6's core `org.protege.editor.owl.explanation` extension point.
On an inferred named `SubClassOf` row, click Protégé's purple **Explain
inference** (`?`) button. If Protégé offers several explanation services,
select **Kobayashi-MaRust native source justifications**. The KM panel shows
the selected entailment, lets the user bound the number of justifications,
runs outside Swing's event thread, and offers cancellation. It labels every
displayed support as verified and subset-minimal and distinguishes a complete
enumeration from a bounded prefix for which more supports may exist.
Cancellation and timeout stop and reap both the `km explain` supervisor and
all native route workers it started, so closing a request cannot leave an
orphaned reasoner consuming memory in the background.

The upstream
[OWL Explanation library](https://github.com/matthewhorridge/owlexplanation)
defines the programmatic interfaces implemented here. The separate upstream
[Protégé Explanation Workbench](https://github.com/protegeproject/explanation-workbench)
does not expose an extension point for registering a custom
`ExplanationGeneratorFactory`; it may still run its generic reasoner-backed
algorithm. KM therefore integrates with Protégé's standard core Explain
action directly, without modifying or pretending to register a provider in
the Workbench.

The advertised surface is exact: only `OWLSubClassOfAxiom` queries whose
subclass and superclass are named classes are accepted. This includes the
`A SubClassOf owl:Nothing` and `owl:Thing SubClassOf owl:Nothing` conventions
above. Property entailments, individual assertions, and subclass axioms with
anonymous class expressions throw `UnsupportedEntailmentException`; neither
the API nor the GUI presents an empty result for these unsupported forms.

## Performance and certification scope

Explanation search may run many complete classifications and is deliberately
bounded. It rebuilds each candidate from source functional syntax so users see
source OWL axioms rather than internal definers, Skolem symbols, or bridge
clauses.

This feature changes orchestration and proof reconstruction only. It does not
change CB rule applicability or the saturation fixpoint, so it creates no new
Lean re-certification obligation.
